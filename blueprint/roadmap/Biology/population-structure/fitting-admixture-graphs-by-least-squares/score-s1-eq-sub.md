# Score S1 as its value at a normal-equation solution minus a quadratic

Let `ι` and `E` be finite sets, `Q` a real `ι × ι` matrix whose inverse is symmetric,
`(Q⁻¹)ᵀ = Q⁻¹`, `B` a real `ι × E` matrix and `f ∈ ℝ^ι`, and let `ℓ̂ ∈ ℝ^E` solve the normal
equations `Bᵀ Q⁻¹ B ℓ̂ = Bᵀ Q⁻¹ f`. Then for every `ℓ ∈ ℝ^E`,
`S1(B ℓ) = S1(B ℓ̂) - ½ (B (ℓ - ℓ̂))ᵀ Q⁻¹ (B (ℓ - ℓ̂))`, where `S1` is the [score](score-s1.md) with
covariance `Q` and estimated statistics `f`: the Pythagorean decomposition behind generalized least
squares. A singular `Q` has inverse `0` by convention; then the hypotheses hold and both sides are
`0`.
