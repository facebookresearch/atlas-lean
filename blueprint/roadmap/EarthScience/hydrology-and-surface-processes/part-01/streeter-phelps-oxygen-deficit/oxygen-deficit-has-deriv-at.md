# The Streeter–Phelps sag curve solves the deficit equation

For positive deoxygenation and reaeration rates `kd > 0` and `ka > 0` with `ka ≠ kd`, and all real
`L0`, `D0` and `t`, the oxygen deficit
`D(t) = D0 * exp (-ka * t) + kd * L0 * (exp (-kd * t) - exp (-ka * t)) / (ka - kd)` has derivative
`kd * L(t) - ka * D(t)` at `t`, where `L(t) = L0 * exp (-kd * t)` is the remaining oxygen demand:
it solves `D' = kd * L - ka * D`.
