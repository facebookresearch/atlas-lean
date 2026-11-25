# Solution of the counterflow exchanger equations

For real `C_h`, `C_c`, `K`, `L`, `T_hi`, `T_ci`, a pair of functions `T_h, T_c : ℝ → ℝ` solves the
counterflow exchanger equations on `[0, L]`, with `x` measured along the hot flow, when
`T_h(0) = T_hi` (hot inlet at `x = 0`), `T_c(L) = T_ci` (cold inlet at `x = L`), and at every
`x ∈ [0, L]`, within `[0, L]` (one-sided at the ends),

`(C_h T_h)' = -K (T_h - T_c)` and `(C_c T_c)' = -K (T_h - T_c)`.

The cold equation has the hot equation's sign because `x` runs against the cold flow. For `L ≥ 0`
the condition only involves the values of `T_h` and `T_c` on `[0, L]`. In the physical reading
`C_h, C_c > 0` and `K = UA / L ≥ 0`.
