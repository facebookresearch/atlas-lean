# Karush–Kuhn–Tucker conditions characterize the constrained maximizers

Let `ι` and `E` be finite sets, `Q` a positive definite real `ι × ι` matrix, `B` a real `ι × E`
matrix and `f ∈ ℝ^ι`, and for `ℓ ∈ ℝ^E` let `g = Bᵀ Q⁻¹ (f - B ℓ)` be the gradient of `ℓ ↦ S1(B ℓ)`,
where `S1` is the [score](score-s1.md) with covariance `Q` and estimated statistics `f`. Then `ℓ` is
a [constrained maximizer](is-constrained-maximizer.md) if and only if `ℓ e ≥ 0`, `g e ≤ 0` and
`ℓ e * g e = 0` for every `e`: feasibility, a nonpositive gradient and complementary slackness.
