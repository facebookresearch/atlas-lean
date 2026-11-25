# Small Lyapunov sublevel sets are forward invariant

Let `e` be a function from the reals to `ℝ⁴` with `e'(t) = f(e(t))` at every `t ≥ 0`, the
derivative taken within `[0, ∞)` (from the right at `t = 0`), where `f` is the
[nonlinear reduced field](nonlinear-reduced-field.md). Let `c ≤ 1/80000`. If the
[Lyapunov function](longitudinal-lyapunov.md) satisfies `V(e(0)) ≤ c`, then `V(e(t)) ≤ c` for
every `t ≥ 0`. The sublevel set lies strictly inside the ball `‖e‖ < 1/100`, where the
[orbital derivative](fderiv-longitudinal-lyapunov-nonlinear-r-2.md) is at most `0`, so the
solution cannot reach the sphere `‖e‖ = 1/100`.
