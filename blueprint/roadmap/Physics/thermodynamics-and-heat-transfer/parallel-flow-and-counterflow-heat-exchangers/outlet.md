# Parallel-flow outlet temperatures in terms of UA

Let `C_h > 0`, `C_c > 0`, `L > 0`, and let `UA`, `T_hi`, `T_ci` be real. If `(T_h, T_c)` is a
[parallel-flow solution](is-parallel-flow-solution.md) on `[0, L]` with conductance per unit length
`K = UA / L`, then

`T_h(L) = T_hi - C_c / (C_h + C_c) · (T_hi - T_ci) · (1 - exp(-UA (1/C_h + 1/C_c)))` and
`T_c(L) = T_ci + C_h / (C_h + C_c) · (T_hi - T_ci) · (1 - exp(-UA (1/C_h + 1/C_c)))`.
