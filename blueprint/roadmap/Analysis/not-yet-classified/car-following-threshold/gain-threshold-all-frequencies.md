# Gain threshold all frequencies

All-frequency gain threshold for the car-following model. For
`lambda > 0` and `T ≥ 0`, the inequality
`omega > 2 * lambda * sin (omega * T)` holds at every positive
frequency `omega` if and only if `lambda * T ≤ 1 / 2`. By the
frequency-response analysis of the model this is the condition
that the transfer denominator never vanishes and the gain stays
strictly below one at every positive frequency; the boundary
`lambda * T = 1 / 2` is included.
