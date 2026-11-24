# Counterflow effectiveness with its equal-capacity branch

For real `NTU` and `C_r`, the counterflow effectiveness is

- `ε_c = (1 - exp(-NTU (1 - C_r))) / (1 - C_r exp(-NTU (1 - C_r)))` when `C_r ≠ 1`;
- `ε_c = NTU / (1 + NTU)` when `C_r = 1`, where the general formula would be `0 / 0`.

Its domain is `NTU ≥ 0`, `0 < C_r ≤ 1`; for `C_r < 1` the denominator is at least `1 - C_r`.
Elsewhere the convention `u / 0 = 0` applies (for example the value is `0` at `C_r = 1`,
`NTU = -1`).
