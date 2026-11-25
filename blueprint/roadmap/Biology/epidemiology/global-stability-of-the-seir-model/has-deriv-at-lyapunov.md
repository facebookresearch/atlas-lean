# Derivative of the Lyapunov function along solutions

Let `(S, E, I, R)` be a [solution](is-solution.md) of the SEIR system with vital dynamics, under
`σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0` and `R₀ > 1`, where `R₀` is the
[basic reproduction number](r0.md) `R₀ = β σ / ((μ + σ) (μ + γ))`. At every `t ≥ 0` with
`S(t), E(t), I(t) > 0`, the function `s ↦ V(S(s), E(s), I(s))`, for the
[Lyapunov function](lyapunov.md) `V`, has the two-sided derivative `V̇(S(t), E(t), I(t))` at `t`,
where `V̇` is the [Lyapunov derivative](lyapunov-deriv.md).
