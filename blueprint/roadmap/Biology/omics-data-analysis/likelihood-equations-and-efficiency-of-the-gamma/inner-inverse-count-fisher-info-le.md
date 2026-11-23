# Efficiency of the count MLE relative to the moment estimator

Let the count law `μX`
have finite fourth moment, let `θ₀ = (a, b)` with `a, b, σ > 0` satisfy the profile-information
condition `σ / (a (b + σ)) < τ`, `τ = E[∑_{j<K} 1/(a + j)²]`, and assume the two regularity
identities of the model at `θ₀`:

* the **information identity** `⟪I z, z⟫ = E ⟪ψ, z⟫²`, `I = countFisherInfo a b σ τ`,
  `ψ = countScore σ θ₀ K` (second Bartlett identity);
* **differentiated unbiasedness of the moment equations**
  `⟪J x, w⟫ = -E[⟪ψ, x⟫ ⟪g, w⟫]`, `J = momJacobian a b σ`, `g = momEstFun σ θ₀ K`, which is
  `∂_θ E_θ[g(θ, K)] = 0` differentiated under the expectation.

Then for every direction `u`, `⟪I⁻¹ u, u⟫ ≤ E ⟪g, (J⁻¹)ᵀ u⟫²`. The left side is the variance of
`⟪Z, u⟫` for the limit `Z ~ N(0, I⁻¹)` of the MLE and the right side that of the limit
`-J⁻¹ N(0, E[g gᵀ])` of the moment estimator (`variance_inner_countMLE_limit_le`): the
asymptotic covariance of the moment estimator dominates the inverse Fisher information in the
Loewner order.

## Sources

- Godambe (1960); the efficiency of the negative binomial moment estimator was studied by Fisher (1941) and Anscombe (1950).
