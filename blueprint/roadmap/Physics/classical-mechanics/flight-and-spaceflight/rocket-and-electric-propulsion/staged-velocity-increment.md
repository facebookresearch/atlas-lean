# Staged velocity increment

Staged burn and jettison accounting. Burns `i ≤ n` on `[0, tb i]` with positive mass, exhaust
speed `ve i` and the reduced law; between burn `i` and burn `i + 1` a jettison with zero relative
velocity from mass `m i (tb i)` to mass `m (i + 1) 0 ≤ m i (tb i)` that conserves momentum. The
velocity gained from the start of burn `0` to the end of burn `n` is the sum of the burn increments
`ve i * log (m i 0 / m i (tb i))`; the jettisoned masses enter no logarithm. Neither the mass drop
nor the sign of the exhaust speeds is needed for the identity: the drop restricts the statement to
jettisons, and the model's positive stage-specific `ve i` are a special case.
