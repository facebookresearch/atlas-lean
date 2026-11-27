# Log-normal risk-neutral law of the terminal price

For real `S0`, `r`, `σ` and `T`, the assumed risk-neutral law of the terminal price (no dividends)
is the law of `e^Y` for `Y` normal with mean `log S0 + (r - σ²/2) T` and variance `max(σ² T, 0)`,
a normal law of variance `0` being the point mass at its mean. For `S0 > 0` and `T ≥ 0` it is the
law of `S_T = S0 exp((r - σ²/2) T + σ √T Z)` with `Z` standard normal. When `σ² T ≤ 0` (that is,
`σ = 0` or `T ≤ 0`) it is the point mass at `e^{log S0 + (r - σ²/2) T}`. For `S0 ≤ 0` the mean
`log S0` is read with the conventions `log 0 = 0` and `log x = log |x|`.
