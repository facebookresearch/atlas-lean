# Processor Bound

The positive processor bound `Φ` holds on `I` if every full window `[t, t + Φ)` of `Φ`
consecutive ticks contained in `I` contains a step by every correct processor. In particular the
first tick is included and `t + Φ` is excluded. This imposes no scheduling condition if there
is no full window or no correct processor. The positive width excludes a zero-length window.
