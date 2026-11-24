# Hot-stream temperature of the counterflow solution

For real `C_h`, `C_c`, `K`, `L`, `T_hi`, `T_ci` and a position `x`, the counterflow hot-stream
temperature is

`T_h(x) = T_hi - (K / C_h) D₀ I(s, x)`,

with `D₀` the [boundary constant](counterflow-inlet-diff.md), `s` the
[counterflow rate](counterflow-rate.md) and `I(s, x)` the
[exponential integral](exp-decay-integral.md). It is meant for `C_h, C_c > 0`; with `u / 0 = 0`,
`K / C_h = 0` when `C_h = 0`.
