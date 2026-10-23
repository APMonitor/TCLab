/*
  TCLab Temperature Control Lab Firmware 2.1.0 -- 2026-10-23
  Based on firmware 2.0.1 by Jeffrey Kantor, Bill Tubbs,
  John Hedengren, and Shawn Summey.

  Target: Arduino Leonardo/Micro (also supports the AVR Uno and Mega).
  Select Arduino Leonardo in the IDE. Use Serial (USB CDC), not Serial1.
  No additional libraries are required.

  IMPORTANT CONFIGURATION:
  - EXTERNAL AREF must be physically connected by the shield. AREF_VOLTS
    must match that voltage. Default is 3.3 V, as in the supplied firmware.
    Set AREF_VOLTS to 1.75 only for hardware providing a 1.75 V reference.
    analogReference(EXTERNAL) does NOT create a reference voltage.
  - Warning: 50 C. Independent, latched heater shutdown: 90 C.
    After both sensors cool to <=85 C, send A to clear the thermal latch.
    These are configurable operating limits, not a hardware safety rating.
  - All heaters turn off after 5 minutes without a valid complete command.
    Periodic T1, T2, SCAN, etc. queries count as host activity. Long-running
    manual heater tests must also keep polling or adjust HOST_TIMEOUT_MS.

  Existing wire formats are preserved for valid commands:
    A          heaters off; clear thermal latch if cool; "Start" or "Fault"
    LED value  LED brightness 0..100 percent for 10 seconds; two decimals
    P1/P2 val  PWM limit 0..255 (defaults 200/100); two decimals
    Q1/Q2 val  heater demand 0..100 percent; three decimals
    Q1B/Q2B val same request, four-byte IEEE-754 little-endian float reply
    R1/R2      applied heater demand (percent); three decimals
    T1/T2      latest sampled temperature (C); three decimals
    T1B/T2B    latest temperature; four-byte float, WITHOUT line ending
    SCAN       T1, T2, Q1, Q2 as four separate text lines
    VER        "TCLab Firmware 2.1.0 <board>"
    X          heaters off; "Stop" (does not clear a thermal latch)

  Commands are case-insensitive; spaces and tabs are accepted. LF, CR,
  and CRLF terminate commands. Empty lines are ignored. Numeric setters
  require a complete finite number; finite out-of-range values are clamped.
  Malformed/oversized input turns both heaters off and replies "ERR".
  Unknown commands turn both heaters off and echo the command token, as
  before. A faulty/overheated lab returns zero for heater-setting replies.
  A can acknowledge a fault only after temperatures are finite and cool.

  LED: dim/bright = heaters off/on; slow blink = temperature warning;
  fast blink = latched thermal fault. Warnings/faults override LED commands.

  Changes from 2.0.1: correct Q2B channel; bounded null-terminated parsing;
  no dynamic String allocation; strict numeric validation; timeout and USB
  disconnect shutdown; immediate PWM limit application; no USB startup
  wait; latched thermal trip; coherent 100 ms temperature sampling; explicit
  AREF/calibration; rollover-safe timers; corrected LED percentage scaling.

  Firmware interlocks cannot protect against every sensor, MCU, or power
  stage failure. No hardware watchdog or automatic fault restart is enabled.
*/

#include <Arduino.h>
#include <ctype.h>
#include <errno.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(__AVR_ATmega328P__) || defined(__AVR_ATmega168__)
  #define TCLAB_BOARD_NAME "Arduino Uno"
#elif defined(__AVR_ATmega32U4__) || defined(__AVR_ATmega16U4__)
  #define TCLAB_BOARD_NAME "Arduino Leonardo/Micro"
#elif defined(__AVR_ATmega1280__) || defined(__AVR_ATmega2560__)
  #define TCLAB_BOARD_NAME "Arduino Mega"
#else
  #error "This firmware supports AVR Uno, Leonardo/Micro, and Mega boards."
#endif

static_assert(sizeof(float) == 4, "Binary protocol requires 32-bit float");

// Shield wiring. A0/A2 explicitly name the analog header pins.
const uint8_t PIN_T1 = A0;
const uint8_t PIN_T2 = A2;
const uint8_t PIN_Q1 = 3;
const uint8_t PIN_Q2 = 5;
const uint8_t PIN_LED = 9;

// Adjust these values to the actual shield and desired operating limits.
constexpr float AREF_VOLTS = 3.3f;
constexpr float T1_CALIBRATION_GAIN = 1.0f;
constexpr float T2_CALIBRATION_GAIN = 1.0f;
constexpr float T1_CALIBRATION_OFFSET_C = 0.0f;
constexpr float T2_CALIBRATION_OFFSET_C = 0.0f;
constexpr float WARNING_T1_C = 50.0f;
constexpr float WARNING_T2_C = 50.0f;
constexpr float TRIP_T1_C = 90.0f;
constexpr float TRIP_T2_C = 90.0f;
constexpr float RESET_T1_C = 85.0f;
constexpr float RESET_T2_C = 85.0f;
const uint32_t HOST_TIMEOUT_MS = 300000UL;  // 5 minutes
const uint32_t SAMPLE_PERIOD_MS = 100UL;
const uint32_t LED_OVERRIDE_MS = 10000UL;
const uint8_t TEMPERATURE_SAMPLES = 10;
const uint8_t HI_LED = 60;
const uint8_t LO_LED = HI_LED / 16;
const size_t RX_CAPACITY = 64;  // Includes the terminating NUL.
const uint8_t RX_BYTES_PER_LOOP = 64;

static_assert(RESET_T1_C < TRIP_T1_C && RESET_T2_C < TRIP_T2_C,
              "Thermal reset thresholds must be below trip thresholds");
static_assert(HOST_TIMEOUT_MS > 0 && TEMPERATURE_SAMPLES > 0,
              "Timeout and sample count must be positive");

float P1 = 200.0f;
float P2 = 100.0f;
float Q1 = 0.0f;
float Q2 = 0.0f;
float T1 = 0.0f;
float T2 = 0.0f;
bool thermalFault = false;
bool temperatureWarning = false;
bool hostTimerActive = false;
bool ledOverrideActive = false;
uint8_t ledOverridePWM = 0;
uint32_t lastHostCommandMs = 0;
uint32_t lastSampleMs = 0;
uint32_t ledOverrideStartedMs = 0;
char rxBuffer[RX_CAPACITY] = {0};
size_t rxLength = 0;
bool discardLine = false;

float clampValue(float value, float upper) {
  if (value < 0.0f) return 0.0f;
  if (value > upper) return upper;
  return value;
}

void setHeater1(float value) {
  Q1 = (thermalFault || !isfinite(value)) ? 0.0f : clampValue(value, 100.0f);
  analogWrite(PIN_Q1, (int)(Q1 * P1 / 100.0f));
}

void setHeater2(float value) {
  Q2 = (thermalFault || !isfinite(value)) ? 0.0f : clampValue(value, 100.0f);
  analogWrite(PIN_Q2, (int)(Q2 * P2 / 100.0f));
}

void stopHeaters() {
  setHeater1(0.0f);
  setHeater2(0.0f);
}

void resetReceiver() {
  rxLength = 0;
  rxBuffer[0] = '\0';
  discardLine = false;
}

// TMP36: 500 mV at 0 C, 10 mV/C. Match the original 1024-count scaling.
float readTemperature(uint8_t pin, float gain, float offset) {
  analogRead(pin);  // Discard first conversion after changing ADC channels.
  uint32_t sum = 0;
  for (uint8_t i = 0; i < TEMPERATURE_SAMPLES; ++i) {
    sum += (uint16_t)analogRead(pin);
  }
  const float rawC = (sum * (AREF_VOLTS * 100.0f / 1024.0f)
                     / TEMPERATURE_SAMPLES) - 50.0f;
  return rawC * gain + offset;
}

void sampleTemperatures(uint32_t now) {
  T1 = readTemperature(PIN_T1, T1_CALIBRATION_GAIN, T1_CALIBRATION_OFFSET_C);
  T2 = readTemperature(PIN_T2, T2_CALIBRATION_GAIN, T2_CALIBRATION_OFFSET_C);
  lastSampleMs = now;
  temperatureWarning = (T1 > WARNING_T1_C || T2 > WARNING_T2_C);
  if (!isfinite(T1) || !isfinite(T2) || T1 >= TRIP_T1_C || T2 >= TRIP_T2_C) {
    thermalFault = true;
  }
  if (thermalFault) stopHeaters();
}

bool safeToClearThermalFault() {
  return isfinite(T1) && isfinite(T2) && T1 <= RESET_T1_C && T2 <= RESET_T2_C;
}

void sendFloatResponse(float value) {
  Serial.println(value, 3);
}

void sendBinaryResponse(float value) {
  // All supported AVR targets use little-endian IEEE-754 32-bit floats.
  Serial.write(reinterpret_cast<const uint8_t *>(&value), sizeof(value));
}

void rejectCommand() {
  stopHeaters();
  Serial.println(F("ERR"));
}

bool isCommandSpace(char c) {
  return c == ' ' || c == '\t';
}

bool parseFiniteNumber(const char *text, float &value) {
  if (*text == '\0') return false;
  // Accept decimal notation, including an optional sign and exponent.
  // Explicit grammar rejects hexadecimal numbers, NAN, INF, and junk suffixes.
  const char *p = text;
  if (*p == '+' || *p == '-') ++p;
  bool hasDigits = false;
  while (*p >= '0' && *p <= '9') { hasDigits = true; ++p; }
  if (*p == '.') {
    ++p;
    while (*p >= '0' && *p <= '9') { hasDigits = true; ++p; }
  }
  if (!hasDigits) return false;
  if (*p == 'e' || *p == 'E') {
    ++p;
    if (*p == '+' || *p == '-') ++p;
    const char *exponentStart = p;
    while (*p >= '0' && *p <= '9') ++p;
    if (p == exponentStart) return false;
  }
  if (*p != '\0') return false;
  char *end = NULL;
  errno = 0;
  const double parsed = strtod(text, &end);
  value = (float)parsed;
  return end != text && *end == '\0' && errno != ERANGE && isfinite(value);
}

void dispatchCommand(char *line, uint32_t now) {
  // Trim leading/trailing horizontal whitespace without allocation.
  while (isCommandSpace(*line)) ++line;
  char *end = line + strlen(line);
  while (end > line && isCommandSpace(end[-1])) --end;
  *end = '\0';
  if (*line == '\0') return;  // Includes the second half of CRLF.

  char *argument = line;
  while (*argument && !isCommandSpace(*argument)) {
    *argument = (char)toupper((unsigned char)*argument);
    ++argument;
  }
  if (*argument) {
    *argument++ = '\0';
    while (isCommandSpace(*argument)) ++argument;
  }

  const bool numeric = strcmp(line, "LED") == 0 || strcmp(line, "P1") == 0
      || strcmp(line, "P2") == 0 || strcmp(line, "Q1") == 0
      || strcmp(line, "Q2") == 0 || strcmp(line, "Q1B") == 0
      || strcmp(line, "Q2B") == 0;
  const bool query = strcmp(line, "A") == 0 || strcmp(line, "X") == 0
      || strcmp(line, "R1") == 0 || strcmp(line, "R2") == 0
      || strcmp(line, "T1") == 0 || strcmp(line, "T2") == 0
      || strcmp(line, "T1B") == 0 || strcmp(line, "T2B") == 0
      || strcmp(line, "SCAN") == 0 || strcmp(line, "VER") == 0;
  float value = 0.0f;
  if (!numeric && !query) {
    stopHeaters();
    Serial.println(line);  // Preserve the unknown-command response.
    return;
  }
  if ((numeric && !parseFiniteNumber(argument, value))
      || (query && *argument != '\0')) {
    rejectCommand();
    return;
  }

  lastHostCommandMs = now;
  hostTimerActive = true;
  if (strcmp(line, "A") == 0) {
    stopHeaters();
    if (safeToClearThermalFault()) thermalFault = false;
    if (thermalFault) Serial.println(F("Fault"));
    else Serial.println(F("Start"));
  } else if (strcmp(line, "X") == 0) {
    stopHeaters();
    Serial.println(F("Stop"));
  } else if (strcmp(line, "LED") == 0) {
    value = clampValue(value, 100.0f);
    ledOverridePWM = (uint8_t)(value * 255.0f / 100.0f + 0.5f);
    ledOverrideStartedMs = now;
    ledOverrideActive = true;
    Serial.println(value, 2);
  } else if (strcmp(line, "P1") == 0) {
    P1 = clampValue(value, 255.0f);
    setHeater1(Q1);  // Apply changed limits even if Q1 is unchanged.
    Serial.println(P1, 2);
  } else if (strcmp(line, "P2") == 0) {
    P2 = clampValue(value, 255.0f);
    setHeater2(Q2);
    Serial.println(P2, 2);
  } else if (strcmp(line, "Q1") == 0 || strcmp(line, "Q1B") == 0) {
    setHeater1(value);
    if (strcmp(line, "Q1B") == 0) sendBinaryResponse(Q1);
    else sendFloatResponse(Q1);
  } else if (strcmp(line, "Q2") == 0 || strcmp(line, "Q2B") == 0) {
    setHeater2(value);  // Corrected: Q2B must never set heater 1.
    if (strcmp(line, "Q2B") == 0) sendBinaryResponse(Q2);
    else sendFloatResponse(Q2);
  } else if (strcmp(line, "R1") == 0) sendFloatResponse(Q1);
  else if (strcmp(line, "R2") == 0) sendFloatResponse(Q2);
  else if (strcmp(line, "T1") == 0) sendFloatResponse(T1);
  else if (strcmp(line, "T2") == 0) sendFloatResponse(T2);
  else if (strcmp(line, "T1B") == 0) sendBinaryResponse(T1);
  else if (strcmp(line, "T2B") == 0) sendBinaryResponse(T2);
  else if (strcmp(line, "SCAN") == 0) {
    sendFloatResponse(T1);
    sendFloatResponse(T2);
    sendFloatResponse(Q1);
    sendFloatResponse(Q2);
  } else if (strcmp(line, "VER") == 0) {
    Serial.println(F("TCLab Firmware 2.1.0 " TCLAB_BOARD_NAME));
  }
}

void readCommands(uint32_t now) {
  // Bound work per loop so continuous input cannot starve safety checks.
  for (uint8_t count = 0; count < RX_BYTES_PER_LOOP && Serial.available() > 0;
       ++count) {
    const int incoming = Serial.read();
    if (incoming < 0) break;
    const char c = (char)incoming;
    if (c == '\r' || c == '\n') {
      if (discardLine) {
        resetReceiver();
        rejectCommand();  // One error per discarded line, no partial execution.
      } else if (rxLength > 0) {
        rxBuffer[rxLength] = '\0';
        dispatchCommand(rxBuffer, now);
        resetReceiver();
      }
      Serial.flush();  // Commit USB responses, including four-byte binaries.
    } else if (!discardLine) {
      if ((incoming < 32 && c != '\t') || incoming > 126
          || rxLength >= RX_CAPACITY - 1) {
        // Stop immediately; keep discarding through the line terminator.
        stopHeaters();
        discardLine = true;
        rxLength = 0;
        rxBuffer[0] = '\0';
      } else {
        rxBuffer[rxLength++] = c;
        rxBuffer[rxLength] = '\0';
      }
    }
  }
}

void updateStatus(uint32_t now) {
  if (ledOverrideActive && (uint32_t)(now - ledOverrideStartedMs) >= LED_OVERRIDE_MS)
    ledOverrideActive = false;
  uint8_t brightness = (Q1 > 0.0f || Q2 > 0.0f) ? HI_LED : LO_LED;
  if (thermalFault) {
    brightness = ((now / 250UL) % 2) ? HI_LED : LO_LED;
  } else if (temperatureWarning) {
    if ((now % 2000UL) < 1000UL)
      brightness = (Q1 > 0.0f || Q2 > 0.0f) ? LO_LED : LO_LED / 4;
  } else if (ledOverrideActive) brightness = ledOverridePWM;
  analogWrite(PIN_LED, brightness);
}

void setup() {
  // Establish safe outputs before initializing USB or sampling sensors.
  digitalWrite(PIN_Q1, LOW);
  digitalWrite(PIN_Q2, LOW);
  pinMode(PIN_Q1, OUTPUT);
  pinMode(PIN_Q2, OUTPUT);
  pinMode(PIN_LED, OUTPUT);
  stopHeaters();
  analogReference(EXTERNAL);
  Serial.begin(115200);
  // No while (!Serial): interlocks must run without a connected host.
  sampleTemperatures(millis());
  updateStatus(millis());
}

void loop() {
  const uint32_t now = millis();
  if ((uint32_t)(now - lastSampleMs) >= SAMPLE_PERIOD_MS) sampleTemperatures(now);
  if (hostTimerActive && (uint32_t)(now - lastHostCommandMs) >= HOST_TIMEOUT_MS) {
    stopHeaters();
    hostTimerActive = false;
    // Incomplete commands time out too, without accepting an oversized tail.
    if (rxLength > 0) {
      rxLength = 0;
      rxBuffer[0] = '\0';
      discardLine = true;
    }
  }
  if (!Serial) {
    // On native USB boards, a closed port disables heaters immediately.
    // The timeout also covers a frozen host whose port remains open.
    stopHeaters();
    hostTimerActive = false;
    resetReceiver();
    for (uint8_t i = 0; i < RX_BYTES_PER_LOOP && Serial.available() > 0; ++i)
      Serial.read();
  } else {
    readCommands(now);
  }
  updateStatus(now);
}
