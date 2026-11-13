# Asymptotic normality of consistent roots of a vector estimating equation

**Asymptotic normality of consistent roots of a vector estimating equation** (multivariate
Z-estimator, Cramér's conditions). Let `X 0, X 1, …` be i.i.d. with law `μX` and let
`ψ : E → 𝓧 → E` be an estimating function with `E ψ θ₀ (X 0) = 0` and finite second moment.
Assume that on the ball of radius `δ > 0` about `θ₀`, `θ ↦ ψ θ x` is differentiable for every
`x` with derivative `Dψ θ x` satisfying the Lipschitz envelope
`‖Dψ θ x - Dψ θ₀ x‖ ≤ M x ‖θ - θ₀‖` for an integrable `M`; that `Dψ θ₀` is strongly measurable
and integrable; and that `D := E Dψ θ₀ (X 0)` is **nonsingular** (`IsUnit D`). Let `θhat n`
solve the estimating equation `∑_{i<n} ψ θ (X i) = 0` with probability tending to one and
converge to `θ₀` in probability; consistency and the existence of roots are hypotheses, not
consequences. Then `√n (θhat n - θ₀) → -D⁻¹ Y` in distribution, where `Y ~ N(0, E ψ ψᵀ)` is
given through the laws of its projections `⟪Y, t⟫ ~ N(0, E ⟪ψ θ₀, t⟫²)`.

`θ₀` must be an interior point (the ball of radius `δ` lies in the parameter domain of `ψ`);
boundary parameters are not covered.

## Sources

- van der Vaart (1998), Theorem 5.41; Lehmann & Casella (1998), Theorem 6.5.1; multivariate form of `MLEAsymptoticNormality.tendstoInDistribution_sqrt_mul_sub_of_estimatingEquation`.
