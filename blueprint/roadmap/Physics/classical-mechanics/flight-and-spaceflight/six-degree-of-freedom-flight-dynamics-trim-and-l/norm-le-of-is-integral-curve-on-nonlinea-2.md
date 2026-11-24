# Forward solutions starting near the trim decay exponentially

Let `e` be a function from the reals to `ℝ⁴` with `e'(t) = f(e(t))` at every `t ≥ 0`, the
derivative taken within `[0, ∞)` (from the right at `t = 0`), where `f` is the
[nonlinear reduced field](nonlinear-reduced-field.md), and with `‖e(0)‖ ≤ 1/400` in the Euclidean
norm. Then for every `t ≥ 0`

`‖e(t)‖ ≤ √8 exp(−t / 8) ‖e(0)‖`.

The solution starts in the [sublevel set](longitudinal-lyapunov-sublevel-spec.md)
`{V ≤ 1/80000}`, which is [forward invariant](maps-to-sublevel-of-is-integral-curve-on.md) and lies
in the ball of radius `1/100`. From the trim, `e(0) = 0`, the bound forces `e(t) = 0`.
