# Quadratic expansion of the log-likelihood ratio, vector parameter

Under the hypotheses
of `VectorInference.tendstoInDistribution_two_mul_logLikelihood_sub` (without the joint
measurability of `p`, the positive definiteness and `dim E ≥ 1`; only nonsingularity of
`I(θ₀)` is used), the likelihood-ratio statistic at the root minus the null-information Wald
statistic tends to `0` in probability:
`2 (ℓₙ(θhat n) - ℓₙ(θ₀)) - n ⟪I(θ₀) (θhat n - θ₀), θhat n - θ₀⟫ → 0`,
`ℓₙ θ = ∑_{i<n} log p θ (X i)`. This is the vector form of
`LikelihoodRatioTests.tendstoInMeasure_two_mul_logLikelihood_sub_sub`.

## Sources

- the second-order expansion of Wilks (1938); van der Vaart (1998), Theorem 16.7.
