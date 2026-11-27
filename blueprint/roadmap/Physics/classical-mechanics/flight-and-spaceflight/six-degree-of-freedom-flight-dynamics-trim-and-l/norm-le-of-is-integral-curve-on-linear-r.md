# Forward solutions of the linear plant decay exponentially

Let `e` be a function from the reals to `ℝ⁴` with `e'(t) = A e(t)` at every `t ≥ 0`, the
derivative taken within `[0, ∞)` (from the right at `t = 0`), where `A e` is the
[reduced linear plant](linear-reduced-field.md). Then for every `t ≥ 0`, with `‖·‖` the Euclidean
norm,

`‖e(t)‖ ≤ √8 exp(−t / 4) ‖e(0)‖`.

Along the solution the [Lyapunov function](longitudinal-lyapunov.md) has the
[derivative](fderiv-longitudinal-lyapunov-linear-redu.md) `−‖e‖² ≤ −V / 2`, so `V` decays at least
as `exp(−t / 2)`, and the [comparison bounds](longitudinal-lyapunov-bounds.md) give the factor
`√(2 / (1/4)) = √8`. From the trim, `e(0) = 0`, the bound forces `e(t) = 0`.
