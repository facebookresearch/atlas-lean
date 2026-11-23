# The scaled chain settles near the endemic equilibrium

Combine Kurtz's theorem with the
global stability of the endemic equilibrium (`SEIRVital.IsSolution.tendsto_endemic`): if
`σ > 0`, `γ ≥ 0`, `μ > 0`, `R₀ = β σ / ((μ + σ) (μ + γ)) > 1`, the ODE solution starts in the
open positive orthant and the scaled initial state converges to it in probability, then for
every `ε > 0` there is `t₀` such that at each fixed time `t ≥ t₀`,

`P(|S(t)/N - S*| + |E(t)/N - E*| + |I(t)/N - I*| ≥ ε) → 0`  as `N → ∞`,

where `(S*, E*, I*)` is the endemic equilibrium at scale `1`. The limit is `N → ∞` at fixed `t`;
nothing is claimed uniformly in `t`.
