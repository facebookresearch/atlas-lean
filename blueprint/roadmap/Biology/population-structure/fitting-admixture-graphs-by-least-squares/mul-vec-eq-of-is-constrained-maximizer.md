# For positive definite covariance all maximizers give the same fit

Let `ι` and `E` be finite sets, `Q` a positive definite real `ι × ι` matrix, `B` a real `ι × E`
matrix and `f ∈ ℝ^ι`. If `ℓ₁` and `ℓ₂` are [constrained maximizers](is-constrained-maximizer.md) of
the [score](score-s1.md) `S1` with covariance `Q` and estimated statistics `f`, then `B ℓ₁ = B ℓ₂`:
every constrained maximizer gives the same predicted statistics.
