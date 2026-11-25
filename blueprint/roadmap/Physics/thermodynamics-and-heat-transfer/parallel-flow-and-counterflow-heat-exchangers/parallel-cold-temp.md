# Cold-stream temperature of the parallel-flow solution

For real `C_h`, `C_c`, `K`, inlet temperatures `T_hi`, `T_ci` and a position `x`, the parallel-flow
cold-stream temperature is

`T_c(x) = T_ci + C_h / (C_h + C_c) · (T_hi - T_ci) · (1 - exp(-r x))`,

with `r` the [parallel-flow decay rate](parallel-decay-rate.md). It is meant for `C_h, C_c > 0`;
with the convention `u / 0 = 0`, the fraction `C_h / (C_h + C_c)` is `0` when `C_h + C_c = 0`.
