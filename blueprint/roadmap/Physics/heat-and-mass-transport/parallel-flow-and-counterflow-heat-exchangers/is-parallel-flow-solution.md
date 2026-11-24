# Solution of the parallel-flow exchanger equations

For real `C_h`, `C_c`, `K`, `L`, `T_hi`, `T_ci`, a pair of functions `T_h, T_c : ℝ → ℝ` solves the
parallel-flow exchanger equations on `[0, L]` when `T_h(0) = T_hi`, `T_c(0) = T_ci` (both inlets at
`x = 0`), and at every `x ∈ [0, L]`, within `[0, L]` (one-sided at the ends),

`(C_h T_h)' = -K (T_h - T_c)` and `(C_c T_c)' = K (T_h - T_c)`.

For `L ≥ 0` the condition only involves the values of `T_h` and `T_c` on `[0, L]`. In the physical
reading `C_h, C_c > 0` are the stream capacity rates and `K = UA / L ≥ 0` the conductance per unit
length; there is no phase change and no axial conduction.
