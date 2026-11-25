# A constrained maximizer exists for every positive definite covariance

Let `ι` and `E` be finite sets, `Q` a positive definite real `ι × ι` matrix, `B` any real `ι × E`
matrix and `f ∈ ℝ^ι`. Then there is a [constrained maximizer](is-constrained-maximizer.md): a vector
`ℓ ∈ ℝ^E` with `ℓ e ≥ 0` for every `e` and `S1(B ℓ') ≤ S1(B ℓ)` for every nonnegative `ℓ'`, where
`S1` is the [score](score-s1.md) with covariance `Q` and estimated statistics `f`. No full-rank or
other condition on `B` is needed.
