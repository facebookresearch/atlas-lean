# Asymptotic normality of the misspecified MLE

**Asymptotic normality of the misspecified MLE** (White 1982, Theorem 3.2). Let
`X 0, X 1, …` be IID with an arbitrary law `μX` (not assumed to belong to any model), `ℓ θ x` a
log-likelihood, and `est` a maximum-likelihood estimator on a compact `K ⊆ E`, a.e. strongly
measurable. Assume:

* **Wald conditions**: `θ ↦ ℓ θ x` continuous on `K`, the uniform LLN on `K`, and a unique
  maximizer `θstar` of the expected log-likelihood on `K` (the pseudo-true value, equivalently the
  Kullback–Leibler projection, `isIdentifiedOn_popCrit_iff_isKLProjectionOn`), lying in the
  **interior** of `K`;
* **score**: on the ball of radius `δ > 0` about `θstar`, `ℓ · x` has gradient `ψ θ x`, with
  `‖ψ θ x‖ ≤ G x` for an integrable `G`, `ℓ θ` a.e. strongly measurable and `ℓ θstar` integrable;
* **Cramér conditions** on `ψ` as in the vector Z-estimator theorem, and a nonsingular
  `A = E Dψ θstar`.

Then `√n (est n - θstar) ⇒ Z` for every `Z` with `⟪Z, t⟫ ~ N(0, ⟪A⁻¹ B A⁻ᵀ t, t⟫)`, where
`A⁻¹ B A⁻ᵀ = GEE.sandwichCovariance A B` and `B = covarianceOperator (μX.map (ψ θstar))`. The
estimating equation `E ψ θstar = 0`, the root of the likelihood equation and the consistency of
`est` are derived, not assumed.
