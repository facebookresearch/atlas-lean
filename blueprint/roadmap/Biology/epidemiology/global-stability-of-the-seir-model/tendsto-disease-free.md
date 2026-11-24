# Convergence to the disease-free state when R₀ ≤ 1

Let [solution](is-solution.md) `(S, E, I, R)` of the SEIR system with vital dynamics, under `β ≥ 0`,
`σ > 0`, `γ ≥ 0`, `μ > 0`, `N > 0` and `R₀ ≤ 1`, where `R₀` is the
[basic reproduction number](r0.md) `R₀ = β σ / ((μ + σ) (μ + γ))`, with `S(0), E(0), I(0) > 0`. Then
`(S(t), E(t), I(t)) → (N, 0, 0)` as `t → ∞`. This covers `R₀ = 1`. Only solutions starting in the
open positive orthant are covered; initial states on its boundary are not.
