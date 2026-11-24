# Coolant outlet temperature

For real `ṁ`, `cp`, `q₀`, `Lₑ`, `L` and `T_in`, the coolant outlet temperature is

`T_out = T_in + 2q₀Lₑ sin(πL/(2Lₑ))/(π ṁ cp)`.

It is intended for `ṁ > 0` and `cp > 0`. With `x/0 = 0` it is `T_in` when `ṁ = 0` or `cp = 0`;
blocked flow with positive heating has no steady state, so that value is not a prediction.
