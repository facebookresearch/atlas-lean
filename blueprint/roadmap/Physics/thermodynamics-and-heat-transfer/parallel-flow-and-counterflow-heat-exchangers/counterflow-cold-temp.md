# Cold-stream temperature of the counterflow solution

For real `C_h`, `C_c`, `K`, `L`, `T_hi`, `T_ci` and a position `x`, the counterflow cold-stream
temperature is

`T_c(x) = T_hi - D₀ - (K / C_c) D₀ I(s, x)`,

with `D₀` the [boundary constant](counterflow-inlet-diff.md), `s` the
[counterflow rate](counterflow-rate.md) and `I(s, x)` the
[exponential decay formula](exp-decay-integral.md); since `I(s, 0) = 0`, `T_c(0) = T_hi - D₀` is the
cold outlet value. It is meant for `C_h, C_c > 0`; with `u / 0 = 0`, `K / C_c = 0` when `C_c = 0`.
