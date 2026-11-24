# Asymptotic normality of a consistent root of a cluster estimating equation

In sandwich form: let clusters `X 0, X 1, …` be IID with law `μC` (no independence is
assumed within a cluster: `ψ` consumes the whole cluster), and let
`ψ : E → 𝓒 → E` satisfy, for every cluster and every `θ` in the ball of radius
`δ > 0` about `θ₀`: `θ ↦ ψ θ x` is differentiable with derivative `Dψ θ x` obeying the
Lipschitz uniform remainder `‖Dψ θ x - Dψ θ₀ x‖ ≤ M x ‖θ - θ₀‖` for an integrable `M`.
Assume `E ψ θ₀ = 0` with finite second moment, `Dψ θ₀` strongly measurable and
integrable, and the limiting Jacobian `A = E Dψ θ₀` **nonsingular**. Let `θhat n` solve
`∑_{i<n} ψ θ (X i) = 0` with probability tending to one and converge to `θ₀` in
probability. Then `√n (θhat n - θ₀) ⇒ Z` in distribution, where
`⟪Z, t⟫ ~ N(0, ⟪A⁻¹ B A⁻ᵀ t, t⟫)`, where `B` is the second-moment operator of the cluster score `ψ θ₀`. All clusters share the law `μC`; cluster laws that vary between clusters or with `n`
are not covered.
