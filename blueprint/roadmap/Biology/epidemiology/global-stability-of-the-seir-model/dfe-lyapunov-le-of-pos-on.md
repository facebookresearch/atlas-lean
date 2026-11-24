# The disease-free Lyapunov function does not increase while positive

Let [solution](is-solution.md) `(S, E, I, R)` of the SEIR system with vital dynamics, with `σ > 0`,
`γ ≥ 0`, `μ > 0`, `N > 0` and `R₀ ≤ 1`, where `R₀` is the [basic reproduction number](r0.md)
`R₀ = β σ / ((μ + σ) (μ + γ))`. If `t ≥ 0` and `S(s), E(s), I(s) > 0` for every `s ∈ [0, t]`, then
`V₀(S(t), E(t), I(t)) ≤ V₀(S(0), E(0), I(0))` for the
[disease-free Lyapunov function](dfe-lyapunov.md) `V₀`.
