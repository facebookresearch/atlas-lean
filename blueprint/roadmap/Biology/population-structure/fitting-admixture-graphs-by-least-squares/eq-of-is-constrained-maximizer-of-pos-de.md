# A positive definite Gram matrix makes the constrained maximizer unique

Let `ι` and `E` be finite sets, `Q` a positive definite real `ι × ι` matrix, `B` a real `ι × E`
matrix such that the Gram matrix `Bᵀ Q⁻¹ B` is positive definite, and `f ∈ ℝ^ι`. If `ℓ₁` and `ℓ₂`
are [constrained maximizers](is-constrained-maximizer.md) of the [score](score-s1.md) `S1` with
covariance `Q` and estimated statistics `f`, then `ℓ₁ = ℓ₂`: any two constrained maximizers are
equal. Since a constrained maximizer [exists](exists-is-constrained-maximizer.md) for every positive
definite `Q`, it is then unique.
