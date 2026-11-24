# Departures

Cumulative departures by time `s` from the signal queue: the arrivals minus the vehicles
still queued, `lam * s - queueLen lam mu R s`, as an `ℝ≥0` count through `Real.toNNReal`
(exact on the admitted domain `0 < lam < mu`).
