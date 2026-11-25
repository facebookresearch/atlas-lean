# Forward solutions exist from states near the trim

For every initial state `e₀ ∈ ℝ⁴` with Euclidean norm `‖e₀‖ ≤ 1/400` there is a function `e` from
the reals to `ℝ⁴` with `e(0) = e₀` and `e'(t) = f(e(t))` at every `t ≥ 0`, the derivative taken
within `[0, ∞)` (from the right at `t = 0`), where `f` is the
[nonlinear reduced field](nonlinear-reduced-field.md), and with the coordinates of `e(t)` in the
[actuator box](actuator-box.md) for every `t ≥ 0`. The maximal solution in `ℝ × {‖e‖ < 1/100}`
keeps `V ≤ 1/80000` by sublevel invariance, so for every `T ≥ 0` it never leaves the compact set
`[0, T] × {V ≤ 1/80000}`, and by the
[compact-exit theorem](../../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md)
it is defined on all of `[0, ∞)`.
