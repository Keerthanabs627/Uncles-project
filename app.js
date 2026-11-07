// ver 2.25 change format of dashboard
// - Monthly rollover for log files
// - REST API used to write to smartEvse along with MQTT publish
const express = require('express');
const axios = require('axios');
const mqtt = require('mqtt');
const { exec } = require('child_process');
const fs = require('fs');
const path = require('path');

const app = express();
const port = 3000;

require('dotenv').config();

// --- CONFIGURATION ---
const LOG_FILE = path.join(__dirname, process.env.LOG_FILE);
const SHELLY_PRO_EM50_IP = process.env.SHELLY_PRO_EM50_IP;
const COS_STVS_IP = process.env.COS_STVS_IP;
const COS_EV_IP = process.env.COS_EV_IP;
const COS_REST_LOADS_IP = process.env.COS_REST_LOADS_IP;
const SHELLLY_PRO_3EM_GRID_IP = process.env.SHELLLY_PRO_3EM_GRID_IP;
const EV_AMPS_IP = process.env.EV_AMPS_IP; // Shelly Gen1 em50 IoT
const AC_IP = process.env.AC_IP;    // IP if Shelly Pro4PM controlling the AC units
const WTR_HTR_IP = process.env.WTR_HTR_IP;  // IP of Shelly Plus1PM controlling the Water HTR
const SCOOTER_IP = process.env.SCOOTER_IP;  // IP of Shelly Plus1PM controlling the Scooter
const PUMP_IP = process.env.PUMP_IP;    // IP of Shelly Plus1PM controlling the Pump
const PYTHON_SCRIPT = process.env.PYTHON_SCRIPT;
const MQTT_URL = process.env.MQTT_URL;
const MQTT_OPTIONS = { username: process.env.MQTT_USERNAME, password: process.env.MQTT_PASSWORD };
const EVSE_TOPIC_BASE = process.env.EVSE_TOPIC_BASE;
const HEARTBEAT_TOPIC = process.env.HEARTBEAT_TOPIC;
const SMARTEVSE_IP = process.env.SMARTEVSE_IP;
const SMARTEVSE_BASE_URL = `http://${SMARTEVSE_IP}`;
const MANAGED_TOPIC = process.env.MANAGED_TOPIC;

// --- LOGGING UTILITY ---
function logEvent(message) {
    const now = new Date();
    const dateStr = now.toLocaleDateString();
    const timeStr = now.toLocaleTimeString();
    const entry = `[${dateStr} ${timeStr}] ${message}\n`;

    try {
        if (fs.existsSync(LOG_FILE)) {
            const stats = fs.statSync(LOG_FILE);
            const mtime = new Date(stats.mtime);

            // Check if last modification was in a different calendar month or year
            if (mtime.getFullYear() !== now.getFullYear() || mtime.getMonth() !== now.getMonth()) {
                const ext = path.extname(LOG_FILE);
                const base = path.basename(LOG_FILE, ext);
                const dir = path.dirname(LOG_FILE);

                const lastYear = mtime.getFullYear();
                const lastMonth = String(mtime.getMonth() + 1).padStart(2, '0');
                const archiveName = `${base}_${lastYear}-${lastMonth}${ext}`;
                const archivePath = path.join(dir, archiveName);

                // Roll over the old log file by renaming it
                fs.renameSync(LOG_FILE, archivePath);

                // Initialize the new month's log file
                fs.writeFileSync(LOG_FILE, `--- New Log Started for ${dateStr} ---\n`);
            }
        }

        fs.appendFileSync(LOG_FILE, entry);
        console.log(`LOG: ${message}`);
    } catch (err) {
        console.error("Logging Error:", err.message);
    }
}

// Updated Global State additions
let lastActionTs = 0;
let lastPauseTs = 0;
let lastActionWatrHtrTs = 0;
const MIN_A = 6.0;  // do not go below 6.0A for EVSE override_current
const MAX_A = 14.0;
const TARGET_FREQ_MIN = 50.4;
const TARGET_FREQ_MAX = 50.7;
const NORMAL_SETTLING_MS = 1 * 60 * 1000;  // 1 min
const HIGH_SOC_SETTLING_MS = 5 * 60 * 1000; // 5 min
const STUDER_MAX_W = 4000;  // do not go above 4000W for Studer
const STUDER_MIN_W = 2600;  // Allow loading 1400W below Maximum

const ENABLED_TIME_RANGE = {
    startTime: "09:00:00",
    endTime: "17:00:00"
};

let studer_call_ok = true; // Flag to indicate if Studer data call via xcom-lan was ok

// --- COS HYSTERESIS CONFIGURATION & TRACKING STATE ---
const COS_HYSTERESIS_MS = 10 * 60 * 1000; // 10 minutes hysteresis to prevent rapid ON/OFF and mechanical relay damage
let lastCosEvOnTs = 0;        // Timestamp when COS EV switch was last turned ON
let lastCosRestLoadsOnTs = 0; // Timestamp when COS Rest Loads switch was last turned ON
let lastCosStvsOnTs = 0;      // Timestamp when COS Stvs switch was last turned ON

// --- PUMP CONTROL CONFIGURATION & TRACKING STATE ---
let pumpActiveStartTs = null;    // Timestamp when pump actually started drawing power > 50W
let pumpLockoutStartTs = null;   // Timestamp when pump controller was shut down due to time limit
let pumpDryRunLockout = false;   // Track if pump is locked out due to dry-running
let pumpDryRunStartTs = null;    // Timestamp when pump power first fell below dry-run threshold
let pumpLastOnTs = null;         // Timestamp when pump was last ON (drawing power > 50W)
const PUMP_ACTIVE_POWER_W = 50;  // Power threshold to determine if pump is active (above noise level)
const PUMP_DRY_RUN_W = 500;      // Power threshold below which active pump is considered running dry
const PUMP_LOCKOUT_MS = 5 * 60 * 1000;     // Lockout duration (5 minutes)
const PUMP_MAX_RUN_MS = 60 * 60 * 1000;    // Maximum run time (60 minutes)
const PUMP_GRACE_PERIOD_MS = 20 * 1000;    // Grace period for initial power draw settling (20 seconds)
const PUMP_DRY_RUN_TIME_MS = 60 * 1000;    // Dry run threshold duration (60 seconds)
const PUMP_INACTIVITY_THRESHOLD_HOURS = process.env.PUMP_INACTIVITY_THRESHOLD_HOURS ? Number(process.env.PUMP_INACTIVITY_THRESHOLD_HOURS) : 12; // Suggested threshold: 12 hours
const PUMP_INACTIVITY_THRESHOLD_MINS = PUMP_INACTIVITY_THRESHOLD_HOURS * 60; // Inactivity threshold in minutes (720m)
const appStartTs = Date.now();   // Application start timestamp for inactivity fallback
let pumpInactivityAlarmLogged = false; // Prevent log spamming for inactivity alarm

let isEvseDataFresh = false;
let evseMqttTimeout = null;

// List of devices - This method of acces is for the future and yet TBD
// Currently all these devices are hardcoded in the script
let devices = [
    {
        'device_name': 'cos-stvs',
        'device_ip': COS_STVS_IP,
        'device_type': 'shelly-plus-1pm',
        'channel_id': 0,
        'device_enabled': true,
        'description': 'When the device is switched ON the supply to the Stoves is from the Grid otherwise from Solar'
    },
    {
        'device_name': 'cos-rest-loads',
        'device_ip': COS_REST_LOADS_IP,
        'device_type': 'shelly-plus-1pm',
        'channel_id': 0,
        'device_enabled': true,
        'description': 'When the device is switched ON the supply to the Rest Loads is from the Grid otherwise from Solar'
    },
    {
        'device_name': 'cos-ev',
        'device_ip': COS_EV_IP,
        'device_type': 'shelly-plus-1pm',
        'channel_id': 0,
        'device_enabled': true,
        'description': 'When the device is switched ON the supply to the EV is from the Grid otherwise from Solar'
    },
    {
        'device_name': 'smartevse-current',
        'device_ip': SMARTEVSE_IP,
        'device_type': 'smart-evse-controller',
        'device_enabled': true,
        'description': 'Override Current from 6A to 14A in 1A steps.'
    },
    {
        'device_name': 'smartevse-mode',
        'device_ip': SMARTEVSE_IP,
        'device_type': 'smart-evse-controller',
        'device_enabled': true,
        'description': 'mode is programmable between Normal, and Pause for load management purposes. Off is not allowed by this service.'
    },
    {
        'device_name': 'ac_sr_daikin',
        'device_ip': AC_IP,
        'device_type': 'shelly-pro-4pm',
        'channel_id': 3,                    // SR Daikin AC unit on channel 3 of the Shelly Pro 4PM
        'device_enabled': true,
        'description': 'When the device is switched ON the AC unit cools the room'
    },
    {
        'device_name': 'water_heater',
        'device_ip': WTR_HTR_IP,
        'device_type': 'shelly-plus-1pm',
        'device_enabled': true,
        'description': 'When the device is switched ON the water heater heats the water using its autonomous thermostat based control'
    },
    {
        'device_name': 'scooter',
        'device_ip': SCOOTER_IP,
        'device_type': 'shelly-plus-1pm',
        'channel_id': 0,
        'device_enabled': true,
        'description': 'When the device is switched ON the scooter is charged'
    },
    {
        'device_name': 'pump',
        'device_ip': PUMP_IP,
        'device_type': 'shelly-plus-1pm',
        'channel_id': 0,
        'device_enabled': true,
        'description': 'When the device is switched ON the pump controller is enabled'
    }
];

// This method of priority management is not yet implemented.
let priority = ['cos_stvs',
    'cos_rest_loads',
    'cos_ev',
    'smartevse-current',
    'smartevse-mode',
    'ac_sr_daikin',
    'water_heater',
    'scooter',
    'pump'
];


let state = {
    ts: "",                         // timestamp of the last update
    status_msg: "Initializing",       // status message of the system
    enabled: true,                    // whether the system is enabled
    solar: null,                    // solar data from mystuder.py
    isEvseDataFresh: false,         // Whether EVSE data is fresh
    studer_call_ok: false,          // Whether Studer data call via xcom-lan was ok
    managed: {},
    evse: {
        mode: "Unknown",            // mode of the EVSE
        override_current: 60,       // current override for the EVSE
        actual_charge_current: 0,   // actual charge current for the EVSE
        plug_state: "Unknown",    // plug state of the EVSE
        connected: false,
        pauseToNormal: "Waiting for excess solar",
        evse_on_solar_drawing_power: false,
        ev_system_control_disabled: false,   // Disable EV system control
        status_over_lan: null
    },
    shelly: {
        ch0_enphase: 0,             // Enphase MPPT power
        ch1_total: 0,               // total power
        studer_only_w: 0,           // Studer power = ch1_total - ch0_enphase
        cos_ev_state: null,          // EVSE COS state
        cos_rest_loads_state: null,   // Rest of the loads COS state
        cos_stvs_state: null,       // Stvs COS state
        grid_status: null,          // Shelly Pro3EM Grid Status
        grid_available: true,        // Grid availability state based on phase voltages
        grid_power: 0,              // Total grid power in Watts
        freq: 0,                    // frequency as measured by Shelly ProEM50
        ac_power: 0,                // AC power consumption
        ac_en: false,               // AC is enabled
        water_heater_power: 0,      // Water heater power consumption
        water_heater_en: false,     // Water heater is enabled
        scooter_power: 0,           // Scooter power consumption
        scooter_en: false,          // scooter is enabled
        water_pump_power: 0,        // Water pump power consumption
        water_pump_en: false,       // water pump is enabled
        water_pump_active_minutes: 0, // Water pump active minutes this cycle
        water_pump_lockout_minutes: 0, // Water pump lockout minutes this cycle
        water_pump_lockout: false,    // Water pump lockout state
        water_pump_dry_run_lockout: false, // Water pump dry run lockout state
        water_pump_last_on_ts: null,  // Timestamp (ms) when pump was last ON
        water_pump_last_on_time: null, // Formatted time string when pump was last ON
        water_pump_duration_since_last_on_mins: 0, // Minutes elapsed since pump was last ON
        water_pump_inactivity_alarm: false, // Alarm indicator if duration exceeds threshold
        EmergencyCosRestLoadsSwitched: false, // Tracks if the rest of the loads COS has been switched off due to emergency
        EmergencyCosEvSwitched: false, // Tracks if the EV COS has been switched off due to emergency
        EmergencyCosStvsSwitched: false      // Tracks if the stvs COS has been switched off due to emergency
    }
};



const MQTT_ALLOWED_DELAY_EVSE = 1 * 60 * 1000; // 2 minutes

const client = mqtt.connect(MQTT_URL, MQTT_OPTIONS);

// Helpers for Formatting
const fmtW = (val) => Math.round(val || 0).toLocaleString() + " W";
const fmtA = (val) => (val || 0).toFixed(1) + " A";
const fmtHz = (val) => (val || 0).toFixed(1) + " Hz";
const fmtSOC = (val) => (val || 0).toFixed(1) + " %";
const fmtV = (val) => (val || 0).toFixed(1) + " V";

// Connect to MQTT Broker and on success subscribe to the specified topics
client.on('connect', () => {
    logEvent("Connected to MQTT Broker");
    client.subscribe([
        `${EVSE_TOPIC_BASE}/Mode`,
        `${EVSE_TOPIC_BASE}/ChargeCurrentOverride`,
        `${EVSE_TOPIC_BASE}/ChargeCurrent`,
        `${EVSE_TOPIC_BASE}/EVPlugState`,
        `${EVSE_TOPIC_BASE}/connected`,
        `${MANAGED_TOPIC}`
    ]);
    resetEvseHeartbeatTimer();
});

// On message received from the specified topics, update the state and log the event if the value has changed.
// Also update the timestamp of last action for the EVSE, this is used to determine if the EVSE is still connected.
client.on('message', (topic, message) => {
    const val = message.toString();
    const prevMode = state.evse.mode;

    switch (topic) {
        case `${EVSE_TOPIC_BASE}/Mode`:
            state.evse.mode = val;
            if (prevMode !== "Unknown" && prevMode !== val) logEvent(`SmartEVSE Mode Changed: ${prevMode} -> ${val}`);
            isEvseDataFresh = true;
            state.isEvseDataFresh = true;
            resetEvseHeartbeatTimer();
            break;
        case `${EVSE_TOPIC_BASE}/ChargeCurrentOverride`: state.evse.override_current = parseInt(val);
            state.isEvseDataFresh = true;
            isEvseDataFresh = true;
            resetEvseHeartbeatTimer();
            break;
        case `${EVSE_TOPIC_BASE}/EVPlugState`: state.evse.plug_state = val; break;
        case `${EVSE_TOPIC_BASE}/connected`: state.evse.connected = (val === "true"); break;
        case `${MANAGED_TOPIC}`:
            managed = JSON.parse(val);
            state.managed = managed;
            break;

    }
    state.ts = new Date().toLocaleString();
});

/**
 * Reset the EVSE heartbeat timer
 * This function should be called every time we receive a message from the EVSE
 */
function resetEvseHeartbeatTimer() {
    // 1. Clear the previous timer so it doesn't trigger prematurely
    if (evseMqttTimeout) {
        clearTimeout(evseMqttTimeout);
    }

    // 2. Set a new timer. If 2min pass without a reset, data is stale
    evseMqttTimeout = setTimeout(() => {
        isEvseDataFresh = false;
        state.isEvseDataFresh = false;
        logEvent('Missed heartbeat! Existing EVSE state data is now STALE.');
    }, MQTT_ALLOWED_DELAY_EVSE);
}

/**
 * Render the UI
 */
function renderUI() {
    let html = fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8');
    const isGrid = state.shelly.cos_ev_state === true;
    const isRestGrid = state.shelly.cos_rest_loads_state === true;
    const battCurrent = state.solar?.batt_current || 0;
    const battVolts = state.solar?.batt_voltage || 0;
    const battWatts = battCurrent * battVolts;
    const pv_current_now_total = state.solar?.pv_current_now_total || 0;
    const studerSolarWatts = pv_current_now_total * battVolts;
    const studerOnlyWatts = (state.shelly.ch1_total - state.shelly.ch0_enphase) ? (state.shelly.ch1_total - state.shelly.ch0_enphase) : 0;
    const totalSolarW = state.shelly.ch0_enphase + studerSolarWatts;

    // Grid status & color logic
    const gridAvailable = state.shelly.grid_available;
    const gridPowerW = state.shelly.grid_power || 0;
    const gridPowerKw = `${(gridPowerW / 1000).toFixed(2)} kW`;
    const hasGridPower = gridPowerW > 50;

    const gridIconColor = gridAvailable ? "#e67e22" : "#e74c3c"; // Orange if available/active, Red if unavailable
    const gridStatusText = gridAvailable ? "GRID AVAILABLE" : "GRID UNAVAILABLE";
    const vA = state.shelly.grid_status?.a_voltage || 0;
    const vB = state.shelly.grid_status?.b_voltage || 0;
    const vC = state.shelly.grid_status?.c_voltage || 0;
    const gridVoltage = state.shelly.grid_status ? `${vA.toFixed(0)}V / ${vB.toFixed(0)}V / ${vC.toFixed(0)}V` : "N/A";
    const gridArrowColor = hasGridPower ? "#e67e22" : "#95a5a6";
    const gridArrowIcon = hasGridPower ? "fa-arrow-down arrow-down" : "fa-xmark";

    // Solar icon & arrow colors (Green when active, Gray when 0W)
    const solarIconColor = totalSolarW > 0 ? "#27ae60" : "#7f8c8d";
    const solarArrowColor = totalSolarW > 0 ? "#27ae60" : "#95a5a6";

    // Inverter color (Red on overload, Green on solar, Orange on grid)
    const studerOverload = state.shelly.studerOverLoad;
    const inverterColor = studerOverload ? "#e74c3c" : (totalSolarW > 0 ? "#27ae60" : "#e67e22");

    // Battery state, colors and dynamic arrows
    let battColor = "#95a5a6";
    let battArrowIcon = "fa-minus";
    let battArrowColor = "#95a5a6";
    let battArrowLabel = "IDLE";

    if (battCurrent > 0.5) {
        battColor = "#27ae60"; // Charging Green
        battArrowIcon = "fa-arrow-down";
        battArrowColor = "#27ae60";
        battArrowLabel = "CHARGING";
    } else if (battCurrent < -0.5) {
        battColor = "#e67e22"; // Discharging Orange
        battArrowIcon = "fa-arrow-up";
        battArrowColor = "#e67e22";
        battArrowLabel = "DISCHARGING";
    } else {
        const soc = state.solar?.batt_soc || 0;
        battColor = soc > 50 ? "#27ae60" : (soc > 20 ? "#f39c12" : "#e74c3c");
    }

    // Load icon and arrow colors (Green on solar, Orange on grid)
    const loadIconColor = isRestGrid ? "#e67e22" : "#27ae60";
    const loadArrowColor = isRestGrid ? "#e67e22" : "#27ae60";
    const loadSourceLabel = isRestGrid ? "GRID" : "SOLAR";

    // EVSE icon color: Green if Normal on solar, Orange if Normal on grid, Red if Pause or Off
    let evseIconColor = "#e74c3c";
    if (state.evse.mode === "Normal") {
        evseIconColor = isGrid ? "#e67e22" : "#27ae60";
    }

    // Helper to format minutes duration into readable string
    const fmtDuration = (totalMins) => {
        if (totalMins === null || totalMins === undefined) return "N/A";
        const mins = Math.round(totalMins);
        if (mins < 60) return `${mins}m`;
        const h = Math.floor(mins / 60);
        const m = mins % 60;
        return m > 0 ? `${h}h ${m}m` : `${h}h`;
    };

    const now = Date.now();
    const effectiveLastOnTs = pumpLastOnTs || appStartTs;
    const isPumpRunningNow = state.shelly.water_pump_en && (pumpActiveStartTs !== null);
    const durationSinceLastOnMins = isPumpRunningNow ? 0 : Math.round(((now - effectiveLastOnTs) / (60 * 1000)) * 10) / 10;
    const isPumpAlarm = durationSinceLastOnMins >= PUMP_INACTIVITY_THRESHOLD_MINS;
    const lastTimeStr = pumpLastOnTs ? `Last: ${fmtDuration(durationSinceLastOnMins)} ago` : `Boot: ${fmtDuration(durationSinceLastOnMins)} ago`;

    // Pump status and colors
    let pumpStatus = "OFF";
    let pumpStatusColor = "#e74c3c"; // Red when OFF
    if (state.shelly.water_pump_en) {
        if (pumpActiveStartTs !== null) {
            const activeMins = ((Date.now() - pumpActiveStartTs) / 60000).toFixed(1);
            pumpStatus = `ON (${activeMins}m)`;
            pumpStatusColor = isRestGrid ? "#e67e22" : "#27ae60"; // Green on solar, Orange on grid
        } else {
            if (isPumpAlarm) {
                pumpStatus = `STANDBY &bull; <span style="color:#e74c3c; font-weight:700;"><i class="fa-solid fa-triangle-exclamation"></i> ALARM: Inactive ${fmtDuration(durationSinceLastOnMins)}</span>`;
                pumpStatusColor = "#e74c3c"; // Alarm Red
            } else {
                pumpStatus = `STANDBY (${lastTimeStr})`;
                pumpStatusColor = "#f1c40f"; // Yellow on standby
            }
        }
    } else if (pumpLockoutStartTs !== null) {
        const lockoutElapsed = Date.now() - pumpLockoutStartTs;
        const remainingMs = PUMP_LOCKOUT_MS - lockoutElapsed;
        if (remainingMs > 0) {
            const remSecs = Math.ceil(remainingMs / 1000);
            const mins = Math.floor(remSecs / 60);
            const secs = remSecs % 60;
            pumpStatus = `LOCKOUT (${mins}m ${secs}s)`;
            pumpStatusColor = "#e74c3c"; // Red on lockout
        }
    } else if (state.shelly.water_pump_dry_run_lockout) {
        pumpStatus = "DRY RUN LOCKOUT";
        pumpStatusColor = "#e74c3c"; // Red
    }

    if (!state.shelly.water_pump_en && isPumpAlarm) {
        pumpStatus = `${pumpStatus} &bull; <span style="color:#e74c3c; font-weight:700;"><i class="fa-solid fa-triangle-exclamation"></i> ALARM: Inactive ${fmtDuration(durationSinceLastOnMins)}</span>`;
    }

    // Sub-system devices: Blue when ON but < 50W, Green on solar (>= 50W), Orange on grid (>= 50W), Red when OFF
    const getDeviceColor = (isEnabled, powerW) => {
        if (!isEnabled) return "#e74c3c"; // OFF -> Red
        if ((powerW || 0) < 50) return "#3b82f6"; // ON but < 50W -> Blue
        return isRestGrid ? "#e67e22" : "#27ae60"; // ON and >= 50W -> Grid (Orange) / Solar (Green)
    };

    const wtrHtrColor = getDeviceColor(state.shelly.water_heater_en, state.shelly.water_heater_power);
    const acColor = getDeviceColor(state.shelly.ac_en, state.shelly.ac_power);
    const scooterColor = getDeviceColor(state.shelly.scooter_en, state.shelly.scooter_power);

    const replacements = {
        appBtnColor: state.enabled ? '#e74c3c' : '#27ae60',
        appBtnText: state.enabled ? 'DISABLE APP' : 'ENABLE APP',
        status_msg: state.status_msg,
        ts: state.ts,
        gridIconColor: gridIconColor,
        gridStatusText: gridStatusText,
        gridVoltage: gridVoltage,
        gridPowerKw: gridPowerKw,
        gridArrowColor: gridArrowColor,
        gridArrowIcon: gridArrowIcon,
        solarIconColor: solarIconColor,
        solarArrowColor: solarArrowColor,
        enphase_w: fmtW(state.shelly.ch0_enphase),
        studer_solar_w: fmtW(studerSolarWatts),
        total_solar_w: fmtW(totalSolarW),
        inverterColor: inverterColor,
        studer_only_w: fmtW(studerOnlyWatts),
        ac_freq: (state.solar?.ac_freq_out || 0).toFixed(2),
        battArrowIcon: battArrowIcon,
        battArrowColor: battArrowColor,
        battArrowLabel: battArrowLabel,
        loadIconColor: loadIconColor,
        loadArrowColor: loadArrowColor,
        loadSourceLabel: loadSourceLabel,
        batt_soc: (state.solar?.batt_soc || 0).toFixed(1),
        battColor: battColor,
        batt_current: fmtA(battCurrent),
        batt_voltage: fmtV(battVolts),
        batt_w: fmtW(battWatts),
        total_house_w: fmtW(state.shelly.ch1_total),
        total_rest_w: fmtW(state.shelly.total_rest_loads),
        evseIconColor: evseIconColor,
        chargerIconColor: evseIconColor,
        evse_power: fmtW(state.evse.actual_charge_power),
        evse_current: fmtA(state.evse.actual_charge_current),
        evse_mode: state.evse.mode,
        evse_override: (state.evse.override_current / 10).toFixed(1),
        evse_plug_state: state.evse.plug_state,
        sourceTagColor: isGrid ? '#e67e22' : '#27ae60',
        sourceIcon: isGrid ? 'fa-tower-broadcast' : 'fa-sun',
        sourceText: isGrid ? 'POWER SOURCE: GRID' : 'POWER SOURCE: SOLAR',
        toggleButtonHtml: (state.evse.mode === "Pause" || state.evse.mode === "Off") ? `
            <form action="/api/toggle-pause-off" method="POST" style="margin-top:5px; display:inline-block;">
                <button class="btn btn-sm" style="background: #7f8c8d; padding: 6px 12px; font-size: 0.85em;">TOGGLE TO ${state.evse.mode === "Pause" ? "OFF" : "PAUSE"}</button>
            </form>
        ` : '',
        pump_status: pumpStatus,
        pump_status_color: pumpStatusColor,
        pump_w: fmtW(state.shelly.water_pump_power),
        wtrHtrColor: wtrHtrColor,
        wtr_htr_status: state.shelly.water_heater_en ? "ON" : "OFF",
        wtr_htr_color: wtrHtrColor,
        wtr_htr_w: fmtW(state.shelly.water_heater_power),
        acColor: acColor,
        ac_status: state.shelly.ac_en ? "ON" : "OFF",
        ac_color: acColor,
        ac_w: fmtW(state.shelly.ac_power),
        scooterColor: scooterColor,
        scooter_status: state.shelly.scooter_en ? "ON" : "OFF",
        scooter_color: scooterColor,
        scooter_w: fmtW(state.shelly.scooter_power)
    };

    for (const [key, value] of Object.entries(replacements)) {
        html = html.replace(new RegExp(`{{${key}}}`, 'g'), value);
    }
    return html;
}

/**
 * Get solar data from mystuder.py script. Includes handling forStuder data not being fresh
 * @returns {Promise<object|null>}
 */
async function getSolarData() {
    return new Promise((resolve) => {
        exec(PYTHON_SCRIPT, (error, stdout) => {
            if (error) {
                // include time in HH:MM:SS format with error message in the log
                console.error("Python Exec Error:", new Date().toLocaleString(), error.message);
                state.studer_call_ok = false;
                return resolve(null);
            }
            if (!stdout || stdout.trim() === "") {
                console.error("Python Output Empty");
                state.studer_call_ok = false;
                return resolve(null);
            }
            try {
                const raw = JSON.parse(stdout);
                state.studer_call_ok = true;
                resolve(raw);
            } catch (e) {
                console.error("JSON Parse Error:", e.message, "Output was:", stdout);
                state.studer_call_ok = false;
                resolve(null);
            }
        });
    });
}

/**
 * Switches a Shelly Plus 1 device ON or OFF using the Switch.Set RPC method.
 * 
 * @param {string} ip - The IP address of the Shelly Plus 1 device.
 * @param {boolean|string|number} desiredState - The desired state to set (true/ON or false/OFF).
 * @param {string} switchName - The name of the switch to set.
 * @returns {Promise<boolean>} - Returns true if the operation succeeded and switch was set to the desired state.
 */
async function setShellySwitchState(ip, desiredState, switchName) {
    // Determine target boolean value for the switch
    let onValue = false;
    if (typeof desiredState === 'boolean') {
        onValue = desiredState;
    } else if (typeof desiredState === 'string') {
        const normalized = desiredState.trim().toLowerCase();
        onValue = (normalized === 'on' || normalized === 'true' || normalized === '1');
    } else if (typeof desiredState === 'number') {
        onValue = (desiredState === 1);
    }

    // Enforce Hysteresis before turning any COS OFF (from Grid back to Solar)
    if (!onValue) {
        let lastOnTs = 0;
        let cosLabel = "";
        if (ip === COS_EV_IP) { lastOnTs = lastCosEvOnTs; cosLabel = "COS_EV"; }
        else if (ip === COS_REST_LOADS_IP) { lastOnTs = lastCosRestLoadsOnTs; cosLabel = "COS_REST_LOADS"; }
        else if (ip === COS_STVS_IP) { lastOnTs = lastCosStvsOnTs; cosLabel = "COS_STVS"; }

        const elapsed = Date.now() - lastOnTs;
        if (elapsed < COS_HYSTERESIS_MS) {
            const remainingSecs = Math.ceil((COS_HYSTERESIS_MS - elapsed) / 1000);
            // COS hysterysis not allowing to turn the COS OFF, hence return
            return false;
        }
    }

    const url = `http://${ip}/rpc/Switch.Set?id=0&on=${onValue}`;
    try {
        logEvent(`Setting Shelly Plus 1 switch controlling ${switchName} at ${ip} to ${onValue ? 'ON' : 'OFF'} using Switch.Set...`);
        const response = await axios.get(url, { timeout: 1000 });

        // Gen2 Switch.Set returns a JSON like {"was_on": boolean} on success
        if (response.status === 200 && response.data) {
            logEvent(`Successfully switched Shelly Plus 1 switch controlling ${switchName} at ${ip} to ${onValue ? 'ON' : 'OFF'}. Response: ${JSON.stringify(response.data)}`);

            // Record timestamp if successfully turned ON
            if (onValue) {
                if (ip === COS_EV_IP) lastCosEvOnTs = Date.now();
                else if (ip === COS_REST_LOADS_IP) lastCosRestLoadsOnTs = Date.now();
                else if (ip === COS_STVS_IP) lastCosStvsOnTs = Date.now();
            }
            return true;
        }
        throw new Error(`Invalid response status: ${response.status}`);
    } catch (e) {
        logEvent(`Failed to switch Shelly Plus 1 controlling ${switchName} at ${ip}: ${e.message}`);
        return false;
    }
}

/**
 * Monitors the water pump's autonomous behavior, checks runtime and dry-run safety limits,
 * and enforces lockout and power-restoration cycles.
 */
async function checkPumpControl(isPumpDataFresh = true) {
    if (!isPumpDataFresh) {
        return;
    }

    const isEn = state.shelly.water_pump_en;
    const power = state.shelly.water_pump_power;
    const now = Date.now();

    // 0. Dry-Run Lockout Handling
    if (pumpDryRunLockout) {
        if (isEn) {
            // User manually turned it ON, clear dry-run lockout
            logEvent(`[Pump Control] Dry-run lockout cleared manually: pump controller detected ON.`);
            pumpDryRunLockout = false;
            state.shelly.water_pump_dry_run_lockout = false;
        } else {
            // Lockout active: pump controller is OFF as expected.
            state.status_msg = `Water Pump is OFF - Dry Run Lockout active.`;
            return;
        }
    }

    // 1. Lockout Handling (Excessive run time)
    if (pumpLockoutStartTs !== null) {
        const lockoutTimeElapsed = now - pumpLockoutStartTs;
        if (lockoutTimeElapsed < PUMP_LOCKOUT_MS) {
            // Lockout active: if Shelly switch is turned ON, force it back OFF
            state.shelly.water_pump_lockout = true;
            state.shelly.water_pump_lockout_minutes = Math.ceil(lockoutTimeElapsed / (60 * 1000));
            if (isEn) {
                logEvent(`[Pump Control] Force-shutting down pump: attempt to operate during active 5-minute lockout.`);
                await setShellySwitchState(PUMP_IP, false, 'Water Pump');
                state.shelly.water_pump_en = false;
                state.shelly.water_pump_power = 0;
            }
            return;
        } else {
            // Lockout expired: auto-restore power to the pump controller
            logEvent(`[Pump Control] Lockout expired. Restoring power to pump controller.`);
            pumpLockoutStartTs = null;
            state.shelly.water_pump_lockout = false;
            state.shelly.water_pump_lockout_minutes = 0;
            const success = await setShellySwitchState(PUMP_IP, true, 'Water Pump');
            if (success) {
                state.shelly.water_pump_en = true;
            }
        }
    }

    // 2. Anomaly Handling: Precautionary Power ON
    // If pump controller is OFF, but no active run-time lockout or dry-run lockout exists
    if (!isEn && pumpLockoutStartTs === null && !pumpDryRunLockout) {
        logEvent(`[Pump Control] Anomaly detected: pump controller is OFF without active lockout. Initiating precautionary power ON.`);
        const success = await setShellySwitchState(PUMP_IP, true, 'Water Pump');
        if (success) {
            state.shelly.water_pump_en = true;
        }
        return;
    }

    // 3. Active Run and Safety Monitoring
    // Pump is considered actively running if the Shelly switch is ON and power draw exceeds the noise threshold (50W)
    const isPumpRunning = isEn && (power > PUMP_ACTIVE_POWER_W);

    if (isPumpRunning) {
        pumpLastOnTs = now;
        pumpInactivityAlarmLogged = false; // Reset log trigger once pump operates
        if (pumpActiveStartTs === null) {
            // Transition: Pump was idle/OFF, now active
            pumpActiveStartTs = now;
            logEvent(`[Pump Control] Pump started running. Power: ${power}W. Active timer started.`);
        } else {
            // Already running: check running duration
            const runningTimeMs = now - pumpActiveStartTs;
            const runningMinutes = runningTimeMs / (60 * 1000);
            state.shelly.water_pump_active_minutes = runningMinutes;

            // Safety check 1: 60-minute limit exceeded
            if (runningTimeMs > PUMP_MAX_RUN_MS) {
                logEvent(`[Pump Control] Run limit exceeded: pump active for ${runningMinutes.toFixed(1)} mins (max 60m). Shutting down for 5-minute cooling period.`);
                await setShellySwitchState(PUMP_IP, false, 'Water Pump');
                state.shelly.water_pump_en = false;
                state.shelly.water_pump_power = 0;
                pumpActiveStartTs = null;
                pumpLockoutStartTs = now;
                return;
            }

            // Safety check 2: Dry-run protection (active after 20-second grace period)
            if (runningTimeMs > PUMP_GRACE_PERIOD_MS) {
                if (power < PUMP_DRY_RUN_W) {
                    if (pumpDryRunStartTs === null) {
                        pumpDryRunStartTs = now;
                        logEvent(`[Pump Control] Pump power ${power}W is below dry-run threshold of ${PUMP_DRY_RUN_W}W. Starting 60s dry-run timer.`);
                    } else if (now - pumpDryRunStartTs >= PUMP_DRY_RUN_TIME_MS) {
                        logEvent(`[Pump Control] EMERGENCY SHUTDOWN: Dry-run detected! Active power ${power}W has been below ${PUMP_DRY_RUN_W}W threshold for at least 60s.`);
                        await setShellySwitchState(PUMP_IP, false, 'Water Pump');
                        state.shelly.water_pump_en = false;
                        state.shelly.water_pump_power = 0;
                        pumpActiveStartTs = null;
                        pumpDryRunStartTs = null;
                        pumpDryRunLockout = true;
                        state.shelly.water_pump_dry_run_lockout = true;
                        return;
                    }
                } else {
                    if (pumpDryRunStartTs !== null) {
                        logEvent(`[Pump Control] Pump power restored to ${power}W. Resetting dry-run timer.`);
                        pumpDryRunStartTs = null;
                    }
                }

                // Verify expected operating range (around 700W or 1450W)
                const isAround700 = (power >= 550 && power <= 850);
                const isAround1450 = (power >= 1100 && power <= 1650);
                if (!isAround700 && !isAround1450) {
                    logEvent(`[Pump Control] Warning: Pump power draw (${power}W) is outside expected range (around 700W or 1450W).`);
                }
            }
        }
    } else {
        // Pump is not actively running (either Shelly switch is OFF, or power <= 50W)
        if (pumpActiveStartTs !== null) {
            const runningMinutes = ((now - pumpActiveStartTs) / (60 * 1000)).toFixed(1);
            logEvent(`[Pump Control] Pump stopped running. Active run duration was ${runningMinutes} mins.`);
            pumpActiveStartTs = null;
            pumpLastOnTs = now;
        }
        pumpDryRunStartTs = null;
    }

    // 4. Update Pump Inactivity Tracking in State
    const effectiveLastOnTs = pumpLastOnTs || appStartTs;
    const durationSinceLastOnMins = isPumpRunning ? 0 : Math.round(((now - effectiveLastOnTs) / (60 * 1000)) * 10) / 10;
    const isPumpAlarm = durationSinceLastOnMins >= PUMP_INACTIVITY_THRESHOLD_MINS;

    state.shelly.water_pump_last_on_ts = pumpLastOnTs;
    state.shelly.water_pump_last_on_time = pumpLastOnTs ? new Date(pumpLastOnTs).toLocaleString("en-IN", { timeZone: "Asia/Kolkata" }) : "None (since startup)";
    state.shelly.water_pump_duration_since_last_on_mins = durationSinceLastOnMins;
    state.shelly.water_pump_inactivity_alarm = isPumpAlarm;

    // Mirror on root state object
    state.water_pump_last_on_ts = pumpLastOnTs;
    state.water_pump_duration_since_last_on_mins = durationSinceLastOnMins;
    state.water_pump_inactivity_alarm = isPumpAlarm;

    if (isPumpAlarm && !pumpInactivityAlarmLogged) {
        logEvent(`[Pump Control] ALARM: Water pump has been inactive for ${durationSinceLastOnMins.toFixed(1)} mins (exceeds ${PUMP_INACTIVITY_THRESHOLD_HOURS}h threshold).`);
        pumpInactivityAlarmLogged = true;
    }
}

/**
 * Use REST API to get status updates from the Shelly ProEM50 device
 */
async function updateCriticalHardware() {
    // Helper to wrap requests and catch errors individually
    const fetchWithCatch = async (url, label) => {
        try {
            const response = await axios.get(url, { timeout: 500 });
            return response.data;
        } catch (e) {
            console.warn(`⚠️ Timeout or error on device: ${label} -> ${e.message}`);
            return null; // Return null or a fallback default value
        }
    };

    const [res0, res1, resEvSettings] = await Promise.all([
        fetchWithCatch(`http://${SHELLY_PRO_EM50_IP}/rpc/EM1.GetStatus?id=0`, 'Shelly EM1 Ch 0'),
        fetchWithCatch(`http://${SHELLY_PRO_EM50_IP}/rpc/EM1.GetStatus?id=1`, 'Shelly EM1 Ch 1'),
        fetchWithCatch(`http://${SMARTEVSE_IP}/settings`, 'SmartEVSE Settings')
    ]);

    // Safely update state only for devices that successfully responded
    if (res0 && res1) {
        state.shelly.ch0_enphase = res0.act_power;
        state.shelly.ch1_total = res1.act_power;
        state.shelly.studer_only_w = Number((res1.act_power - res0.act_power).toFixed(1));
        state.shelly.freq = res1.freq;  // This is more reliabily available than Studer
    }
    if (resEvSettings) {
        state.evse.status_over_lan = resEvSettings;
    }
}

/**
 * Use REST API to get status updates from all the other Shelly devices
 * The pump controoler is called and state and status and related values published to heartbeat topic
 */
async function updateRestOfTheHardware() {
    // Helper to wrap requests and catch errors individually
    const fetchWithCatch = async (url, label) => {
        try {
            const response = await axios.get(url, { timeout: 500 });
            return response.data;
        } catch (e) {
            console.warn(`⚠️ Timeout or error on device: ${label} -> ${e.message}`);
            return null; // Return null or a fallback default value
        }
    };

    const [resCOS_EV, resCOS_STVS, resEVAmps, resCOS_REST_LOADS, resGrid, resAC, resWtrHtr, resPump, resScooter] = await Promise.all([
        fetchWithCatch(`http://${COS_EV_IP}/rpc/Switch.GetStatus?id=0`, 'COS EV'),
        fetchWithCatch(`http://${COS_STVS_IP}/rpc/Switch.GetStatus?id=0`, 'COS Stvs'),
        fetchWithCatch(`http://${EV_AMPS_IP}/emeter/0`, 'EVSE Amps'),
        fetchWithCatch(`http://${COS_REST_LOADS_IP}/rpc/Switch.GetStatus?id=0`, 'COS Rest Loads'),
        fetchWithCatch(`http://${SHELLLY_PRO_3EM_GRID_IP}/rpc/EM.GetStatus?id=0`, 'Shelly Pro 3EM Grid'),
        fetchWithCatch(`http://${AC_IP}/rpc/Switch.GetStatus?id=3`, 'AC Shelly Pro 4PM'),
        fetchWithCatch(`http://${WTR_HTR_IP}/rpc/Shelly.GetStatus`, 'Water Heater Shelly Plus 1PM'),
        fetchWithCatch(`http://${PUMP_IP}/rpc/Shelly.GetStatus`, 'Water Pump Shelly Plus 1PM'),
        fetchWithCatch(`http://${SCOOTER_IP}/rpc/Shelly.GetStatus`, 'Scooter Shelly Plus 1PM')
    ]);

    // Initialize variable to hold total power supplied by COS Rest Loads
    let total_rest_loads = 0.0;

    // Safely update state only for devices that successfully responded
    if (resCOS_EV) state.shelly.cos_ev_state = resCOS_EV.output;
    if (resEVAmps) {
        state.evse.actual_charge_power = resEVAmps.power;
        state.evse.actual_charge_current = resEVAmps.power / 230;
    }
    if (resCOS_REST_LOADS) state.shelly.cos_rest_loads_state = resCOS_REST_LOADS.output;
    if (resCOS_STVS) state.shelly.cos_stvs_state = resCOS_STVS.output;

    if (resGrid) {
        state.shelly.grid_status = resGrid;
        state.shelly.grid_power = resGrid.total_act_power;

        const vA = resGrid.a_voltage || 0;
        const vB = resGrid.b_voltage || 0;
        const vC = resGrid.c_voltage || 0;

        if (vA < 180 || vB < 180 || vC < 180) {
            if (state.shelly.grid_available) {
                logEvent(`⚠️ Grid failure detected! Phase voltages: A: ${fmtV(vA)}, B: ${fmtV(vB)}, C: ${fmtV(vC)}. Switched to safe mode.`);
            }
            state.shelly.grid_available = false;
        } else {
            state.shelly.grid_available = true;
        }
    }

    if (resAC) {
        state.shelly.ac_power = resAC.apower;
        state.shelly.ac_en = resAC.output;
        total_rest_loads += state.shelly.ac_power;
    }
    if (resWtrHtr) {
        state.shelly.water_heater_power = resWtrHtr["switch:0"].apower;
        state.shelly.water_heater_en = resWtrHtr["switch:0"].output;
        total_rest_loads += state.shelly.water_heater_power;
    }
    let isPumpDataFresh = false;
    if (resPump) {
        state.shelly.water_pump_power = resPump["switch:0"].apower;
        state.shelly.water_pump_en = resPump["switch:0"].output;
        total_rest_loads += state.shelly.water_pump_power;
        isPumpDataFresh = true;
    }

    // Evaluate pump safety and lockout rules
    await checkPumpControl(isPumpDataFresh);

    if (resScooter) {
        state.shelly.scooter_power = resScooter["switch:0"].apower;
        state.shelly.scooter_en = resScooter["switch:0"].output;
        total_rest_loads += state.shelly.scooter_power;
    }
    state.shelly.total_rest_loads = Number(total_rest_loads.toFixed(1));

    // MQTT Heartbeat, format time to Asia/Kolkata HH:MM:SS
    const istTime = new Date().toLocaleString("en-IN", { timeZone: "Asia/Kolkata" });
    if (client.connected) {
        const heartbeat = {
            app_enabled: state.enabled,
            app_status: state.status_msg,
            is_evse_data_fresh: isEvseDataFresh,
            studer_call_ok: state.studer_call_ok,
            solar: state.solar,
            evse: state.evse,
            shelly: state.shelly,
            managed: managed,
            message: state.status_msg,
            timestamp: istTime
        };
        client.publish(HEARTBEAT_TOPIC, JSON.stringify(heartbeat));
    }
}

/**
 * 
 * @param {int} mode_id // 0:OFF, 1:Normal, 4:Pause
 * @param {int} override_current_amps   // actual value of current in amps
 * @returns {Promise<Object>}
 */
async function setSmartEvseModeAndCurrent(mode_id, override_current_amps) {
    const params = {
        mode: mode_id.toString(),
        override_current: Math.round(override_current_amps * 10).toString()
    };

    const url = new URL(`${SMARTEVSE_BASE_URL}/settings`);
    Object.keys(params).forEach(key => url.searchParams.append(key, params[key]));

    let config = {
        method: 'post',
        maxBodyLength: Infinity,
        url: url.toString(),
        headers: {}
    };
    console.log(url.toString());

    try {
        const response = await axios.request(config);
        return response.data;
    }
    catch (error) {
        console.log(error);
        return error;
    }
}

/**
 * 
 * @param {int} mode_id // 0:OFF, 1:Normal, 4:Pause
 * @returns {Promise<Object>}
 */
async function setSmartEvseMode(mode_id) {
    const params = {
        mode: mode_id.toString()
    };

    const url = new URL(`${SMARTEVSE_BASE_URL}/settings`);
    Object.keys(params).forEach(key => url.searchParams.append(key, params[key]));

    let config = {
        method: 'post',
        maxBodyLength: Infinity,
        url: url.toString(),
        headers: {}
    };
    console.log(url.toString());

    try {
        const response = await axios.request(config);
        return response.data;
    }
    catch (error) {
        console.log(error);
        return error;
    }
}

/**
 * 
 * @param {int} override_current_amps   // actual value of current in amps
 * @returns {Promise<Object>}
 */
async function setSmartEvseCurrent(override_current_amps) {
    const params = {
        override_current: Math.round(override_current_amps * 10).toString()
    };

    const url = new URL(`${SMARTEVSE_BASE_URL}/settings`);
    Object.keys(params).forEach(key => url.searchParams.append(key, params[key]));

    let config = {
        method: 'post',
        maxBodyLength: Infinity,
        url: url.toString(),
        headers: {}
    };
    console.log(url.toString());

    try {
        const response = await axios.request(config);
        return response.data;
    }
    catch (error) {
        console.log(error);
        return error;
    }
}


/*
fastHardwareLoop is called every 1.2 seconds and it checks the following:
1. If Studer Overloaded:
    a. if Water Heater is ON, turn it OFF and return
    b. if Studer is still overloaded and Rest of the Loads COS is OFF (on Solar), turn it ON (on Grid) and return
    c. if Studer is still overloaded and Stoves COS is OFF (drawing power from Solar), turn it ON (on Grid) and return
    d. if Studer is still overloaded and EV Charger is drawing power, pause it and reduce the charge current to the Minimum and return
2. TODO
*/
async function fastHardwareLoop() {
    await updateCriticalHardware();

    // Immediate Safety Check: Studer Overload.
    // No data from the EVSE or Studer is required for this check
    // All data is available from Shelly devices locally on LAN using IP
    const studerW = state.shelly.studer_only_w;
    const studerOverLoad = studerW >= STUDER_MAX_W;
    const evse_on_solar_drawing_power = !state.shelly.cos_ev_state && state.evse.actual_charge_power > 500;
    const rest_loads_on_solar_drawing_power = !state.shelly.cos_rest_loads_state && state.shelly.total_rest_loads > 300;
    state.evse.evse_on_solar_drawing_power = evse_on_solar_drawing_power;
    state.shelly.rest_loads_on_solar_drawing_power = rest_loads_on_solar_drawing_power;
    state.shelly.studerOverLoad = studerOverLoad;
    const water_heater_managed_drawing_power_from_solar = managed.water_heater && !state.shelly.cos_rest_loads_state && state.shelly.water_heater_en;

    if (studerOverLoad) {
        // If water heater is drawing power from solar and is managed, turn it off
        if (water_heater_managed_drawing_power_from_solar) {
            const success = await setShellySwitchState(WTR_HTR_IP, false, 'Water Heater');
            if (success) {
                state.shelly.EmergencyWaterHeaterSwitched = true;
            }
            state.status_msg = `EMERGENCY GRID MODE: STUDER OVERLOAD (${fmtW(studerW)})`;
            logEvent(`EMERGENCY GRID MODE TRIGGER: Studer Overload (${fmtW(studerW)}). Setting Water Heater to OFF.`);
            return;
        }
        // else if Rest of the Loads are drawing power from Solar, turn COS_REST_LOADS ON to reduce the load from Solar
        if (rest_loads_on_solar_drawing_power && !state.shelly.EmergencyCosRestLoadsSwitched) {
            // switch COS_REST_LOADS to grid supply to reduce load on Solar
            const success = await setShellySwitchState(COS_REST_LOADS_IP, true, 'COS_REST_LOADS');
            if (success) {
                // set flag to track if COS_REST_LOADS was switched by the emergency mode
                state.shelly.EmergencyCosRestLoadsSwitched = true;
            }
            state.status_msg = `EMERGENCY GRID MODE: STUDER OVERLOAD (${fmtW(studerW)})`;
            logEvent(`EMERGENCY GRID MODE TRIGGER: Studer Overload (${fmtW(studerW)}). Setting COS_REST_LOADS to ON.`);
            return;
        }
        // else if Stoves are drawing power from Solar, turn COS_STVS ON to reduce the load from Solar
        if (!state.shelly.cos_stvs_state && !state.shelly.EmergencyCosStvsSwitched) {
            const success = await setShellySwitchState(COS_STVS_IP, true, 'COS_STVS');
            if (success) {
                // set flag to track if COS_STVS was switched by the emergency mode
                state.shelly.EmergencyCosStvsSwitched = true;
            }
            state.status_msg = `EMERGENCY GRID MODE: STUDER OVERLOAD (${fmtW(studerW)})`;
            logEvent(`EMERGENCY GRID MODE TRIGGER: Studer Overload (${fmtW(studerW)}). Setting COS_STVS to ON.`);
            return;
        }
        // else if EV charger is drawing power from Solar, pause it and reduce the charge current
        if (evse_on_solar_drawing_power) {
            // client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Pause");
            // client.publish(`${EVSE_TOPIC_BASE}/Set/CurrentOverride`, String(MIN_A * 10));
            setSmartEvseModeAndCurrent(4, MIN_A);
            lastPauseTs = Date.now();
            state.status_msg = `EMERGENCY EVSE PAUSE: STUDER OVERLOAD (${fmtW(studerW)})`;
            logEvent(`EMERGENCY TRIGGER: Studer Overload (${fmtW(studerW)}). Pausing Charger`);
            return;
        }
    }

    // any other emergency actions here?
}

/**
 * Checks if the current Asia/Calcutta time is within a given range.
 * @param {string} startTime - "HH:MM:SS"
 * @param {string} endTime - "HH:MM:SS"
 * @returns {boolean}
 */
function isTimeInKolkataRange(startTime, endTime) {
    const now = new Date();

    // Explicitly extract the current time in Asia/Calcutta (Kolkata)
    const kolkataTimeStr = now.toLocaleTimeString('en-US', {
        timeZone: 'Asia/Calcutta',
        hour12: false,
        hour: '2-digit',
        minute: '2-digit',
        second: '2-digit'
    });

    // Helper function to parse "HH:MM:SS" into total seconds
    const timeToSeconds = (timeStr) => {
        const [h, m, s] = timeStr.split(':').map(Number);
        return h * 3600 + m * 60 + s;
    };

    const currentSeconds = timeToSeconds(kolkataTimeStr);
    const startSeconds = timeToSeconds(startTime);
    const endSeconds = timeToSeconds(endTime);

    // Crosses midnight condition (e.g., 23:00 to 06:00)
    if (startSeconds > endSeconds) {
        return currentSeconds >= startSeconds || currentSeconds <= endSeconds;
    }
    // Normal range condition (e.g., 09:00 to 17:00)
    else {
        return currentSeconds >= startSeconds && currentSeconds <= endSeconds;
    }
}

/**
 * Slows down the management loop by running it every 10 seconds.
 * This is mainly done to not load the Studer that also communicates with Studer Servers
 * @returns {void}
 */
async function slowManagementLoop() {
    state.solar = await getSolarData();

    let plug_state = true;

    if (!state.solar) {
        state.status_msg = "Waiting for valid Studer data...";
        return;
    }
    if (typeof state.solar.ac_freq_out === 'undefined') {
        state.status_msg = "Waiting for valid AC Frequency...";
        return;
    }
    if (state.evse.mode === "Unknown") {
        state.status_msg = "Waiting for valid EVSE data...";
        return;
    }
    if (state.evse.plug_state !== "Connected") {
        plug_state = false;
        state.status_msg = "No EV detected - No EV charger management.";
    }

    const now = Date.now();
    const inEnabledTimeRange = isTimeInKolkataRange(ENABLED_TIME_RANGE.startTime, ENABLED_TIME_RANGE.endTime);
    const ev_system_control_disabled = !state.enabled || !inEnabledTimeRange || !plug_state || state.shelly.cos_ev_state;
    const freq = state.solar.ac_freq_out;
    const soc = state.solar.batt_soc;
    const battAmps = state.solar.batt_current;
    const studerW = state.shelly.studer_only_w;
    const currentMode = state.evse.mode;
    const currentOverride = state.evse.override_current / 10;
    const actual_charge_current = state.evse.actual_charge_current;

    state.evse.ev_system_control_disabled = ev_system_control_disabled;

    // 1. EMERGENCY & SAFETY CHECKS (Solar-based)
    const isHighDischarge = battAmps < -30;
    const isMediumDischarge = battAmps < -10;

    /*
    if (!ev_system_control_disabled && isHighDischarge && currentMode === "Normal") {
        state.status_msg = `EMERGENCY PAUSE: BATT DISCHARGE (${fmtA(Math.abs(battAmps))})`;
        logEvent(`EMERGENCY TRIGGER: High Battery Discharge (${fmtA(Math.abs(battAmps))}). Pausing Charger.`);
        // client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Pause");
        // client.publish(`${EVSE_TOPIC_BASE}/Set/CurrentOverride`, String(MIN_A * 10));
        setSmartEvseModeAndCurrent(4, MIN_A);
        lastPauseTs = now;
        return;
    }
    */
    // if battery is discharging and EVSE is drawing more current than MIN_A, reduce it to MIN_A
    if (!ev_system_control_disabled && isMediumDischarge && currentMode === "Normal" && currentOverride > MIN_A) {
        state.status_msg = "SML1: Battery Discharge is Medium. Setting EVSE Current Override to 6A.";
        logEvent(`SML1: Battery Discharge is Medium. Setting EVSE Current Override to 6A.`);
        // client.publish(`${EVSE_TOPIC_BASE}/Set/CurrentOverride`, String(MIN_A * 10));
        setSmartEvseCurrent(MIN_A);
        return;
    }



    // 2. COS Recovery and EVSE NORMAL MODE LOGIC
    const hasStuderMargin = studerW < STUDER_MIN_W;
    const condStandard = (freq >= 50.7 && soc >= 60 && soc <= 95 && battAmps > 25);
    const condFullBatt = (freq >= 50.7 && soc > 95); // Threshold lowered to 50.7 per MD

    // 1st priority to be back on Solar is for COS_STVS_IP to be ON (if it was turned off in Emergency mode)
    // 2nd priority is to be back on Solar is for COS_REST_LOADS_IP to be ON (if it was turned off in Emergency mode)
    // 3rd priority is for EVSE mode to be Normal from Paused state, with 6A minimum current (if it was turned off in Emergency mode)
    if (state.shelly.EmergencyCosStvsSwitched && state.shelly.cos_stvs_state) {
        // if power and frequency conditions permit
        // switch the Stoves to Solar 1st
        if (hasStuderMargin && (condStandard || condFullBatt)) {
            // turn off the COS_STVS_IP switch
            const success = await setShellySwitchState(COS_STVS_IP, false, 'COS Electric Stoves');
            if (success) {
                state.status_msg = `Recovery: Stoves back to solar.`;
                logEvent(`Recovery: Stoves back to solar.`);
                // reset the emergency flag to false
                state.shelly.EmergencyCosStvsSwitched = false;
            }
        }
        else {
            state.status_msg = "EMERGENCY GRID MODE Recovery Stoves: Monitoring for excess solar.";
        }
        return;
    }
    else if (state.shelly.EmergencyCosRestLoadsSwitched && state.shelly.cos_rest_loads_state) {
        // if power and frequency conditions permit
        // switch the Rest of the loads to Solar 2nd priority
        if (hasStuderMargin && (condStandard || condFullBatt)) {
            // turn off the COS_REST_LOADS_IP switch
            const success = await setShellySwitchState(COS_REST_LOADS_IP, false, 'COS Rest of loads');
            if (success) {
                state.status_msg = `Recovery: Rest of the loads back to solar.`;
                logEvent(`Recovery: Rest of the loads back to solar.`);
                // reset the emergency flag to false
                state.shelly.EmergencyCosRestLoadsSwitched = false;
            }
        }
        else {
            state.status_msg = "EMERGENCY GRID MODE Recovery Rest of loads: Monitoring for excess solar.";
        }
        return;
    }
    else if (!ev_system_control_disabled && currentMode === "Pause") {
        // check for delay between pause and resume
        if ((now - lastPauseTs) < 60000) {
            state.evse.pauseToNormal = "Waiting for " + (60000 - (now - lastPauseTs)) / 1000 + " seconds to end";
            return;
        }
        if (hasStuderMargin && (condStandard || condFullBatt)) {
            logEvent(`Start conditions met. Switching to Normal (6A).`);
            // set the current before switching the mode to Normal
            // Use both MQTT and REST API on LAN for robustness
            client.publish(`${EVSE_TOPIC_BASE}/Set/CurrentOverride`, String(MIN_A * 10));
            client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Normal");
            setSmartEvseModeAndCurrent(1, MIN_A);
            lastActionTs = now + 15000; // Initial 15s wait for car to respond
            state.status_msg = "System is ON and Charging at 6A.";
            return;
        }
        state.status_msg = "Paused: Monitoring for excess solar.";
        return;
    }

    // 3. TIMED PAUSE LOGIC (Normal -> Pause)
    if (!ev_system_control_disabled && currentMode === "Normal") {
        const isDischarging12A = battAmps <= -12;
        const isDischarging30A = battAmps <= -30;

        if (soc < 95 && isDischarging12A) {
            if (!state.dischargeStartTime) state.dischargeStartTime = now;
            if ((now - state.dischargeStartTime) / 1000 / 60 >= 30) {
                client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Pause");
                setSmartEvseModeAndCurrent(4, MIN_A);
                logEvent("Battery Discharge >= 12A for 30 mins. Pausing Charger.");
                state.status_msg = "Battery Discharge >= 12A for 30 mins. Pausing Charger.";
                lastPauseTs = now;
                state.dischargeStartTime = null;
                return;
            }
        } else if (soc >= 95 && isDischarging30A) {
            if (!state.dischargeStartTime) state.dischargeStartTime = now;
            if ((now - state.dischargeStartTime) / 1000 / 60 >= 30) {
                logEvent("Battery Discharge >= 30A for 30 mins (High SOC). Pausing Charger.");
                client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Pause");
                setSmartEvseModeAndCurrent(4, MIN_A);
                lastPauseTs = now;
                state.dischargeStartTime = null;
                return;
            }
        } else {
            state.dischargeStartTime = null;
        }
    }

    // 4. CURRENT ADJUSTMENT only if charging is enabled and delay between actions has passed
    if (!ev_system_control_disabled && now > lastActionTs && currentMode === "Normal") {

        // check for 25% on both sides of currentoverride. Use an elegant check for this
        const isDrawing = Math.abs(actual_charge_current - currentOverride) <= (currentOverride * 0.25);
        if (!isDrawing) {
            state.status_msg = "Normal: Waiting for car to draw power...";
            return;
        }

        let newOverride = currentOverride;
        if (freq > TARGET_FREQ_MAX && currentOverride < MAX_A && studerW < (STUDER_MAX_W - 500)) {
            newOverride = currentOverride + 1.0;
        } else if (freq <= TARGET_FREQ_MIN && currentOverride > MIN_A) {
            newOverride = currentOverride - 1.0;
        }

        if (newOverride !== currentOverride) {
            newOverride = Math.max(MIN_A, Math.min(MAX_A, newOverride));
            client.publish(`${EVSE_TOPIC_BASE}/Set/CurrentOverride`, String(Math.round(newOverride * 10)));
            setSmartEvseCurrent(newOverride);
            logEvent(`Adjusting charge current: ${currentOverride}A -> ${newOverride}A (Freq: ${freq}Hz)`);
            const settlingTime = (soc > 95 && Math.abs(battAmps) < 5) ? HIGH_SOC_SETTLING_MS : NORMAL_SETTLING_MS;
            lastActionTs = now + settlingTime;
        } else {
            state.status_msg = `Normal: Stable at ${currentOverride}A (Freq: ${freq}Hz)`;
        }
    }

    // If water heater in the managed object is true AND is OFF and freq is above target max 
    //   AND has enough margin to run the water heater turn on the water heater relay
    // Also ensure that the Water Heater is not switched ON/OFF more thab once every 5 minutes
    //   to prevent Shelly Plus 1PM from toggling too frequenctly due to clouds
    if (now < lastActionWatrHtrTs) return;

    const wtrHtrManagedAndOnSolar = state.managed.water_heater && !state.shelly.cos_rest_loads_state;

    if (wtrHtrManagedAndOnSolar && !state.shelly.water_heater_en && freq > TARGET_FREQ_MAX && studerW < (STUDER_MAX_W - 1000)) {
        // set the water heater relay to true by turning on the WTR_HTR_IP relay
        setShellySwitchState(WTR_HTR_IP, true, 'Water heater');

        // capture the timestamp that the water heater was turned ON in a global variable and add 5m
        lastActionWatrHtrTs = now + 5 * 60 * 1000;

        logEvent("Water heater turned on.");
    }
    // Else IF the water heater is managed and is ON and the freq drops below target max Switch off the water heater
    else if (wtrHtrManagedAndOnSolar && state.shelly.water_heater_en && freq < TARGET_FREQ_MIN) {
        // set the water heater relay to false by turning off the WTR_HTR_IP relay
        setShellySwitchState(WTR_HTR_IP, false, 'Water heater');

        logEvent("Water heater turned off.");
    }
}



// --- WEB SERVER & UI ---

app.post('/api/toggle', (req, res) => {
    if (state.enabled) {
        state.enabled = false;
        logEvent("App manually DISABLED via UI.");
        if (state.evse.mode === "Normal") {
            // USE BOTH MQTT AND REST API ON LAN FOR ROBUSTNESS
            // Set mode to Pause and override current to MIN_A (6A)
            client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Pause");
            client.publish(`${EVSE_TOPIC_BASE}/Set/CurrentOverride`, String(MIN_A * 10));
            setSmartEvseModeAndCurrent(4, MIN_A);
        }
    } else {
        state.enabled = true;
        logEvent("App manually ENABLED via UI.");
    }
    res.redirect('/');
});

app.post('/api/force-off', (req, res) => {
    if (!state.enabled) {
        logEvent("User manually set SmartEVSE to OFF.");
        client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Off");
        setSmartEvseMode(0);
        state.status_msg = "EVSE turned OFF by user.";
    }
    res.redirect('/');
});

app.post('/api/toggle-pause-off', (req, res) => {
    if (state.evse.mode === "Pause") {
        logEvent("Manual Toggle: Pause -> Off");
        client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Off");
        setSmartEvseMode(0);
        state.status_msg = "EVSE toggled from Pause to OFF mode.";
    } else if (state.evse.mode === "Off") {
        logEvent("Manual Toggle: Off -> Pause");
        client.publish(`${EVSE_TOPIC_BASE}/Set/Mode`, "Pause");
        setSmartEvseMode(4);
        state.status_msg = "EVSE toggled from OFF to Pause mode.";
    }
    res.redirect('/');
});

app.get('/', (req, res) => {
    try {
        res.send(renderUI());
    } catch (e) {
        res.status(500).send("Error rendering UI: " + e.message);
    }
});

app.get('/log', (req, res) => {
    if (fs.existsSync(LOG_FILE)) {
        res.type('text/plain').send(fs.readFileSync(LOG_FILE));
    } else {
        res.send("No log file found yet.");
    }
});

app.listen(port, () => {
    logEvent("System Started. Decoupled Logic Active.");
    setInterval(fastHardwareLoop, 1.2 * 1000);
    setInterval(updateRestOfTheHardware, 5 * 1000);
    setInterval(slowManagementLoop, 10 * 1000);
});
