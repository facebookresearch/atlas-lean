# Reynolds stress per unit density: the velocity covariance

Let `(Ω, μ)` be a measure space of flow realizations and `u(ω, τ, y)` a velocity field with values
in `ℝⁿ⁺¹`, for a realization `ω`, a time `τ` and a point `y ∈ ℝⁿ⁺¹`. The Reynolds stress per unit
density at `(τ, y)` is the matrix of covariances of the velocity components,
`Rⱼᵢ(τ, y) = ∫ (uⱼ - ∫ uⱼ dμ) (uᵢ - ∫ uᵢ dμ) dμ`, all functions taken at `(τ, y)`. For a probability
measure and square-integrable components it is `𝔼[u′ⱼ u′ᵢ]`, with the fluctuation `u′ = u - 𝔼[u]`;
otherwise the integrals follow the convention that a non-integrable function has integral `0`.
For a constant density `ρ`, the Reynolds stress proper is `-ρ Rⱼᵢ`.
