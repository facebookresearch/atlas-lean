# Forward solutions that stay in the ball decay exponentially

Let `e` be a function from the reals to `ℝ⁴` with `e'(t) = f(e(t))` at every `t ≥ 0`, the
derivative taken within `[0, ∞)` (from the right at `t = 0`), where `f` is the
[nonlinear reduced field](nonlinear-reduced-field.md), and suppose that `‖e(t)‖ ≤ 1/100` for every
`t ≥ 0`, with `‖·‖` the Euclidean norm. Then for every `t ≥ 0`

`‖e(t)‖ ≤ √8 exp(−t / 8) ‖e(0)‖`.

By the [Lyapunov inequality](fderiv-longitudinal-lyapunov-nonlinear-r-2.md) `V' ≤ −V / 4`, `V`
decays at least as `exp(−t / 4)`, and the [comparison bounds](longitudinal-lyapunov-bounds.md)
give `√(2 / (1/4)) = √8`. Starting in the ball does not imply staying in it, so the hypothesis is
needed.
