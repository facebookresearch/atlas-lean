# The parallel-flow duty is UA times the logarithmic mean difference

Let `C_h > 0`, `C_c > 0`, `L > 0`, and let `UA`, `T_hi`, `T_ci` be real. If `(T_h, T_c)` is a
[parallel-flow solution](is-parallel-flow-solution.md) on `[0, L]` with `K = UA / L`, then the heat
lost by the hot stream is

`C_h (T_hi - T_h(L)) = UA · ΔT_lm`,

with `ΔT_lm` the [logarithmic mean](log-mean-temp-diff.md) of the end differences `T_hi - T_ci` and
`T_h(L) - T_c(L)`, including its equal-difference branch (`UA = 0` or equal inlets). No sign
condition on `UA` is needed.
