# Boundary constant of the counterflow solution

For real `C_h`, `C_c`, `K`, `L`, `T_hi` and `T_ci`, the counterflow boundary constant is

`D₀ = (T_hi - T_ci) / (1 + (K / C_c) I(s, L))`,

with `s` the [counterflow rate](counterflow-rate.md) and `I(s, L)` the
[exponential decay formula](exp-decay-integral.md). With it the closed-form
[hot](counterflow-hot-temp.md) and [cold](counterflow-cold-temp.md) temperatures have
`T_h(0) - T_c(0) = D₀` at the hot inlet, since `I(s, 0) = 0`; for `C_h, C_c > 0`, `K ≥ 0` and
`L ≥ 0` they [solve the counterflow equations](is-counterflow-solution-closed-form.md), the cold
inlet condition `T_c(L) = T_ci` included. Where the denominator vanishes, the convention `u / 0 = 0`
applies.
