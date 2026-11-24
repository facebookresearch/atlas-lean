# For NTU > 0 the C_r = 1 substitution gives 0, not the effectiveness

Let `NTU > 0`. Then substituting `C_r = 1` into the general counterflow formula gives
`(1 - exp(-NTU · 0)) / (1 - 1 · exp(-NTU · 0)) = 0 / 0 = 0` by the convention `u / 0 = 0`, while the
[counterflow effectiveness](counterflow-effectiveness.md) at `C_r = 1` is `NTU / (1 + NTU)`, which
is positive.
