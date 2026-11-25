# For positive initial states, the Lyapunov function stays below its initial value

Let `(S, E, I, R)` be a [solution](is-solution.md) of the SEIR system with vital dynamics, under
`σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0` and `R₀ > 1`, where `R₀` is the
[basic reproduction number](r0.md) `R₀ = β σ / ((μ + σ) (μ + γ))`, with `S(0), E(0), I(0) > 0`. Then
`V(S(t), E(t), I(t)) ≤ V(S(0), E(0), I(0))` for every `t ≥ 0`, for the
[Lyapunov function](lyapunov.md) `V`.
