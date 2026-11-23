# Asymptotic normality of the joint count MLE

Let `X₀, X₁, …` be i.i.d. counts with law
`μX` on `ℕ` with finite second moment, and let `θ₀ = (a, b)`, `a, b, σ > 0`. Assume the
**score equations at the truth** `E[countScore σ θ₀ K] = 0` (Fisher consistency of the shape and
rate equations of `HierarchicalCountMLE`; the rate equation forces the marginal mean
`E K = σ a / b`, `integral_natCast_of_integral_countScore`) and the profile-information condition
`τ = E[∑_{j<K} 1 / (a + j)²] > σ / (a (b + σ))`, which makes the Fisher information
`I = countFisherInfo a b σ τ` invertible. Let `θhat n` be a consistent sequence of roots of the
joint score equations `∑_{i<n} countScore σ θ (X i) = 0`, i.e. of
`shapeScore = rateScore = 0` (`sum_countScore`), with probability tending to one. Then
`√n (θhat n - θ₀) → I⁻¹ Y` in distribution, where `Y ~ N(0, E[ψ ψᵀ])`, `ψ = countScore σ θ₀ K`,
is given through its projections. Under the information identity `E[ψ ψᵀ] = I` this is
`N(0, I⁻¹)` (`tendstoInDistribution_countMLE_of_info`).

## Sources

- Cramér (1946), §33.3; Lehmann & Casella (1998), Theorem 6.5.1; instantiated from `VectorInference.tendstoInDistribution_sqrt_smul_sub_of_estimatingEquation`.
