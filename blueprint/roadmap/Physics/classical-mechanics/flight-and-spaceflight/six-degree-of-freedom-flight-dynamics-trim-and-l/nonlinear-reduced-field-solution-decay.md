# Near the trim a forward solution exists and decays exponentially

For every initial state `e₀ ∈ ℝ⁴` with Euclidean norm `‖e₀‖ ≤ 1/400` there is a function `e` from
the reals to `ℝ⁴` with `e(0) = e₀` and `e'(t) = f(e(t))` at every `t ≥ 0`, the derivative taken
within `[0, ∞)` (from the right at `t = 0`), where `f` is the
[nonlinear reduced field](nonlinear-reduced-field.md), such that for every `t ≥ 0` the coordinates
of `e(t)` lie in the [actuator box](actuator-box.md) and

`‖e(t)‖ ≤ √8 exp(−t / 8) ‖e₀‖`.
