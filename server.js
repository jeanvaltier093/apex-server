/**
 * APEX SERVER - Outil de trading Forex algorithmique
 * Signal BUY: compression de volatilité + breakout + filtres de qualité (D1)
 * Signal SELL: épuisement RSI + haute volatilité + cassure de support (D1)
 *
 * Validé par k-fold temporel (5 folds) sur 7+ ans de données D1, 15 paires.
 * BUY:  WR=56.2% PF=1.99 T=314 (SL=1.5xATR, TP=2.25xATR)
 * SELL: WR=56.0% PF=1.64 T=324 (SL=1.3xATR, TP=1.75xATR)
 */

const express = require('express');
const admin = require('firebase-admin');
const axios = require('axios');

const app = express();
app.use(express.json());

// ─── CORS ─────────────────────────────────────────────────
app.use((req, res, next) => {
  res.header('Access-Control-Allow-Origin', '*');
  res.header('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.header('Access-Control-Allow-Headers', 'Content-Type');
  if (req.method === 'OPTIONS') return res.sendStatus(200);
  next();
});

// ─── Firebase init ────────────────────────────────────────
const serviceAccount = JSON.parse(process.env.FIREBASE_SERVICE_ACCOUNT);
admin.initializeApp({
  credential: admin.credential.cert(serviceAccount),
  databaseURL: 'https://forex-trading-bendo-default-rtdb.firebaseio.com'
});
const db = admin.database();

// ─── Config ───────────────────────────────────────────────
const TWELVE_DATA_KEY = '863b50fb37154d15bc061bc00ed797dc';
const PAIRS = [
  'EUR/USD', 'GBP/USD', 'USD/JPY', 'USD/CHF', 'AUD/USD', 'NZD/USD', 'USD/CAD',
  'EUR/GBP', 'EUR/JPY', 'GBP/JPY', 'EUR/CHF', 'AUD/JPY', 'GBP/CHF', 'EUR/AUD', 'CAD/JPY'
];

// Paramètres BUY validés (D1)
const BUY_CONFIG = {
  squeezeLookback: 50,
  squeezePercentile: 0.20,
  confirmBars: 4,
  trendPeriod: 50,
  excludeVolLookback: 150,
  excludeVolPercentile: 0.8,
  strongTrendLookback: 100,
  strongTrendMaxPct: 8.0,
  slMult: 1.5,
  tpMult: 2.25
};

// Paramètres SELL validés (D1)
const SELL_CONFIG = {
  rsiPeriod: 14,
  rsiOverbought: 64,
  divLookback: 18,
  supportLookback: 3,
  minRise: 0.35,
  volLookback: 100,
  volPercentileMin: 0.4,
  slMult: 1.3,
  tpMult: 1.75
};

const RATE_LIMIT_MS = 10000; // 10s entre appels API (marge de sécurité contre les 429)

// État en mémoire
let lastScanTime = null;
let activeSignals = [];
let scanInProgress = false;

// ─── Indicateurs ──────────────────────────────────────────

function rollingMean(arr, window) {
  const n = arr.length;
  const result = new Array(n).fill(null);
  for (let i = window - 1; i < n; i++) {
    let sum = 0, hasNull = false;
    for (let j = i - window + 1; j <= i; j++) {
      if (arr[j] === null || arr[j] === undefined || isNaN(arr[j])) { hasNull = true; break; }
      sum += arr[j];
    }
    if (!hasNull) result[i] = sum / window;
  }
  return result;
}

function rollingMin(arr, window) {
  const n = arr.length;
  const result = new Array(n).fill(null);
  for (let i = window - 1; i < n; i++) {
    let min = Infinity;
    for (let j = i - window + 1; j <= i; j++) min = Math.min(min, arr[j]);
    result[i] = min;
  }
  return result;
}

function rollingMax(arr, window) {
  const n = arr.length;
  const result = new Array(n).fill(null);
  for (let i = window - 1; i < n; i++) {
    let max = -Infinity;
    for (let j = i - window + 1; j <= i; j++) max = Math.max(max, arr[j]);
    result[i] = max;
  }
  return result;
}

// Percentile rolling: proportion des éléments de la fenêtre >= valeur actuelle
// (réplique exactement (x.iloc[-1] <= x).mean() utilisé dans la validation Python)
function rollingPercentile(arr, window, minPeriods = 20) {
  const n = arr.length;
  const result = new Array(n).fill(null);
  for (let i = window - 1; i < n; i++) {
    const win = arr.slice(i - window + 1, i + 1).filter(v => v !== null && !isNaN(v));
    if (win.length > minPeriods) {
      const current = arr[i];
      const count = win.filter(v => current <= v).length;
      result[i] = count / win.length;
    }
  }
  return result;
}

function computeATR(high, low, close, period = 14) {
  const n = close.length;
  const tr = new Array(n).fill(null);
  for (let i = 0; i < n; i++) {
    if (i === 0) {
      tr[i] = high[i] - low[i];
    } else {
      tr[i] = Math.max(
        high[i] - low[i],
        Math.abs(high[i] - close[i - 1]),
        Math.abs(low[i] - close[i - 1])
      );
    }
  }
  return rollingMean(tr, period);
}

function computeRSI(close, period = 14) {
  const n = close.length;
  const delta = new Array(n).fill(null);
  for (let i = 1; i < n; i++) delta[i] = close[i] - close[i - 1];

  const gain = delta.map(d => (d === null ? null : (d > 0 ? d : 0)));
  const loss = delta.map(d => (d === null ? null : (d < 0 ? -d : 0)));

  const avgGain = rollingMean(gain, period);
  const avgLoss = rollingMean(loss, period);

  const rsi = new Array(n).fill(null);
  for (let i = 0; i < n; i++) {
    if (avgGain[i] !== null && avgLoss[i] !== null) {
      const rs = avgGain[i] / (avgLoss[i] + 1e-9);
      rsi[i] = 100 - 100 / (1 + rs);
    }
  }
  return rsi;
}

function ema(arr, span) {
  const n = arr.length;
  const result = new Array(n).fill(null);
  const alpha = 2 / (span + 1);
  let startIdx = -1;
  for (let i = 0; i < n; i++) {
    if (arr[i] !== null && !isNaN(arr[i])) { startIdx = i; break; }
  }
  if (startIdx === -1) return result;
  result[startIdx] = arr[startIdx];
  for (let i = startIdx + 1; i < n; i++) {
    result[i] = alpha * arr[i] + (1 - alpha) * result[i - 1];
  }
  return result;
}

// ─── Signal BUY : compression de volatilité + breakout ──────

function computeBuySignal(candles) {
  const n = candles.length;
  const close = candles.map(c => c.close);
  const high = candles.map(c => c.high);
  const low = candles.map(c => c.low);
  const open = candles.map(c => c.open);

  const atr = computeATR(high, low, close, 14);
  const atrPercentile = rollingPercentile(atr, BUY_CONFIG.squeezeLookback, 5);

  const isCompressed = atrPercentile.map(v => v !== null && v <= BUY_CONFIG.squeezePercentile);

  const squeezeActive = new Array(n).fill(false);
  for (let i = BUY_CONFIG.confirmBars - 1; i < n; i++) {
    let allCompressed = true;
    for (let j = i - BUY_CONFIG.confirmBars + 1; j <= i; j++) {
      if (!isCompressed[j]) { allCompressed = false; break; }
    }
    squeezeActive[i] = allCompressed;
  }

  const squeezeHigh = rollingMax(high, BUY_CONFIG.confirmBars);
  const emaTrend = ema(close, BUY_CONFIG.trendPeriod);
  const globalVolPct = rollingPercentile(atr, BUY_CONFIG.excludeVolLookback, 20);

  const signal = new Array(n).fill(0);

  for (let i = 1; i < n - 1; i++) {
    if (!squeezeActive[i - 1]) continue;
    if (squeezeHigh[i - 1] === null) continue;
    if (close[i] <= squeezeHigh[i - 1]) continue; // pas de cassure
    if (emaTrend[i] === null || close[i] <= emaTrend[i]) continue; // tendance
    if (close[i] <= open[i]) continue; // followthrough (bougie haussière)

    // Exclusion régime de crise (volatilité globale extrême)
    if (globalVolPct[i] !== null && globalVolPct[i] > BUY_CONFIG.excludeVolPercentile) continue;

    // Exclusion surextension (tendance déjà trop forte)
    if (i >= BUY_CONFIG.strongTrendLookback) {
      const priorClose = close[i - BUY_CONFIG.strongTrendLookback];
      const longTrendPct = ((close[i] - priorClose) / priorClose) * 100;
      if (Math.abs(longTrendPct) > BUY_CONFIG.strongTrendMaxPct) continue;
    }

    signal[i] = 1;
  }

  return { signal, atr };
}

// ─── Signal SELL : épuisement RSI + haute volatilité + cassure support ──

function computeSellSignal(candles) {
  const n = candles.length;
  const close = candles.map(c => c.close);
  const high = candles.map(c => c.high);
  const low = candles.map(c => c.low);

  const atr = computeATR(high, low, close, 14);
  const rsi = computeRSI(close, SELL_CONFIG.rsiPeriod);
  const volPct = rollingPercentile(atr, SELL_CONFIG.volLookback, 20);
  const supportLevel = rollingMin(low, SELL_CONFIG.supportLookback);

  const setupActive = new Array(n).fill(false);
  for (let i = SELL_CONFIG.divLookback; i < n; i++) {
    if (rsi[i] === null || rsi[i] <= SELL_CONFIG.rsiOverbought) continue;
    const priorClose = close[i - SELL_CONFIG.divLookback];
    const rise = ((close[i] - priorClose) / priorClose) * 100;
    if (rise < SELL_CONFIG.minRise) continue;
    if (volPct[i] === null || volPct[i] < SELL_CONFIG.volPercentileMin) continue;
    setupActive[i] = true;
  }

  const signal = new Array(n).fill(0);
  for (let i = 1; i < n; i++) {
    if (!setupActive[i - 1]) continue;
    if (supportLevel[i - 1] === null) continue;
    if (close[i] < supportLevel[i - 1]) {
      signal[i] = -1;
    }
  }

  return { signal, atr };
}

// ─── Récupération des données ────────────────────────────

async function fetchCandles(pair, outputsize = 300) {
  const url = `https://api.twelvedata.com/time_series?symbol=${pair}&interval=1day&outputsize=${outputsize}&apikey=${TWELVE_DATA_KEY}&format=JSON&timezone=UTC`;
  const response = await axios.get(url, { timeout: 15000 });
  const data = response.data;
  if (!data.values) {
    throw new Error(`Twelve Data error for ${pair}: ${data.message || 'unknown'}`);
  }
  const candles = data.values
    .map(v => ({
      datetime: v.datetime,
      open: parseFloat(v.open),
      high: parseFloat(v.high),
      low: parseFloat(v.low),
      close: parseFloat(v.close)
    }))
    .reverse(); // Twelve Data renvoie du plus récent au plus ancien
  // Exclure la dernière bougie (potentiellement non clôturée)
  return candles.slice(0, -1);
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

// ─── Scan principal ───────────────────────────────────────

async function scanAllPairs() {
  if (scanInProgress) {
    console.log(`[${new Date().toISOString()}] Scan déjà en cours, requête ignorée.`);
    return;
  }
  scanInProgress = true;
  console.log(`[${new Date().toISOString()}] Démarrage scan APEX...`);
  const newSignals = [];

  try {
    for (const pair of PAIRS) {
      try {
        const candles = await fetchCandles(pair, 300);
        if (candles.length < 200) {
          console.log(`  ⚠️  ${pair}: pas assez de données (${candles.length})`);
          await sleep(RATE_LIMIT_MS);
          continue;
        }

        const buyResult = computeBuySignal(candles);
        const sellResult = computeSellSignal(candles);

        const lastIdx = candles.length - 1;
        const lastCandle = candles[lastIdx];

        if (buyResult.signal[lastIdx] === 1) {
          const atr = buyResult.atr[lastIdx];
          const entry = lastCandle.close;
          const sl = entry - atr * BUY_CONFIG.slMult;
          const tp = entry + atr * BUY_CONFIG.tpMult;
          newSignals.push({
            pair, direction: 'BUY', entry, sl, tp, atr,
            datetime: lastCandle.datetime,
            key: `${pair.replace('/', '_')}_${lastCandle.datetime}_BUY`
          });
          console.log(`  🟢 BUY signal: ${pair} @ ${entry}`);
        }

        if (sellResult.signal[lastIdx] === -1) {
          const atr = sellResult.atr[lastIdx];
          const entry = lastCandle.close;
          const sl = entry + atr * SELL_CONFIG.slMult;
          const tp = entry - atr * SELL_CONFIG.tpMult;
          newSignals.push({
            pair, direction: 'SELL', entry, sl, tp, atr,
            datetime: lastCandle.datetime,
            key: `${pair.replace('/', '_')}_${lastCandle.datetime}_SELL`
          });
          console.log(`  🔴 SELL signal: ${pair} @ ${entry}`);
        }

      } catch (err) {
        console.error(`  ❌ Erreur ${pair}: ${err.message}`);
      }
      await sleep(RATE_LIMIT_MS);
    }

    lastScanTime = new Date().toISOString();

    // Sauvegarder les nouveaux signaux dans Firebase (sans dupliquer)
    for (const sig of newSignals) {
      const ref = db.ref(`/apex/signals/${sig.key}`);
      const existing = await ref.once('value');
      if (!existing.exists()) {
        await ref.set({ ...sig, result: null, closedAt: null });
        activeSignals.push(sig);
      }
    }

    await db.ref('/apex/summary').update({
      lastScan: lastScanTime,
      pairs: PAIRS.length,
      buyConfig: BUY_CONFIG,
      sellConfig: SELL_CONFIG
    });

    console.log(`[${new Date().toISOString()}] Scan terminé. ${newSignals.length} nouveaux signaux.`);
  } finally {
    scanInProgress = false;
  }
}

// ─── Routes HTTP ──────────────────────────────────────────

app.get('/', (req, res) => {
  res.json({ status: 'APEX online', lastScan: lastScanTime });
});

app.get('/scan', async (req, res) => {
  try {
    await scanAllPairs();
    res.json({ status: 'scan completed', lastScan: lastScanTime });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.get('/summary', async (req, res) => {
  try {
    const signalsSnap = await db.ref('/apex/signals').once('value');
    const signals = signalsSnap.val() || {};
    const allSignals = Object.values(signals);

    const closed = allSignals.filter(s => s.result !== null);
    const active = allSignals.filter(s => s.result === null);

    const wins = closed.filter(s => s.result === 'WIN').length;
    const losses = closed.filter(s => s.result === 'LOSS').length;
    const winRate = closed.length > 0 ? (wins / closed.length) * 100 : null;

    const buyClosed = closed.filter(s => s.direction === 'BUY');
    const sellClosed = closed.filter(s => s.direction === 'SELL');
    const winRateBuy = buyClosed.length > 0
      ? (buyClosed.filter(s => s.result === 'WIN').length / buyClosed.length) * 100 : null;
    const winRateSell = sellClosed.length > 0
      ? (sellClosed.filter(s => s.result === 'WIN').length / sellClosed.length) * 100 : null;

    res.json({
      lastScan: lastScanTime,
      activeSignals: active.length,
      totalClosed: closed.length,
      wins, losses,
      winRate, winRateBuy, winRateSell,
      buyConfig: { slMult: BUY_CONFIG.slMult, tpMult: BUY_CONFIG.tpMult },
      sellConfig: { slMult: SELL_CONFIG.slMult, tpMult: SELL_CONFIG.tpMult },
      pairs: PAIRS.length,
      signals: active
    });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

app.post('/trade/result', async (req, res) => {
  try {
    const { key, result } = req.body;
    if (!key || !['WIN', 'LOSS'].includes(result)) {
      return res.status(400).json({ error: 'key et result (WIN|LOSS) requis' });
    }
    await db.ref(`/apex/signals/${key}`).update({ result, closedAt: new Date().toISOString() });
    res.json({ status: 'updated', key, result });
  } catch (err) {
    res.status(500).json({ error: err.message });
  }
});

// ─── Démarrage ─────────────────────────────────────────────

const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
  console.log(`APEX server démarré sur le port ${PORT}`);
  scanAllPairs().catch(err => console.error('Erreur scan initial:', err));
  // Scan automatique toutes les 4h (cohérent avec le D1, on ne veut pas spammer)
  setInterval(() => {
    scanAllPairs().catch(err => console.error('Erreur scan périodique:', err));
  }, 4 * 60 * 60 * 1000);
});
