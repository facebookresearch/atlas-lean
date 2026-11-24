# Boundary constant of the counterflow solution

For real `C_h`, `C_c`, `K`, `L`, `T_hi` and `T_ci`, the counterflow boundary constant is

`D₀ = (T_hi - T_ci) / (1 + (K / C_c) I(s, L))`,

with `s` the [counterflow rate](counterflow-rate.md) and `I(s, L)` the
[exponential integral](exp-decay-integral.md) `∫₀ᴸ exp(-s y) dy`. It is the temperature difference
`T_h(0) - T_c(0)` at the hot inlet, fixed by the cold inlet condition `T_c(L) = T_ci`. For
`K ≥ 0`, `L ≥ 0` and `C_c > 0` the denominator is at least `1`; elsewhere the convention
`u / 0 = 0` applies.
