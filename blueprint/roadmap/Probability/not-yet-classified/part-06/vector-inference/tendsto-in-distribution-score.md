# Central limit theorem for the score vector

For i.i.d. observations with law
`p θ₀ ν`, a measurable score with mean zero and finite second moment, the normalized score
`n^{-1/2} ∑_{i<n} score p θ₀ (X i)` converges in distribution to `N(0, I(θ₀))`: to any random
vector `Y` all of whose projections `⟪Y, t⟫` are `N(0, ⟪I(θ₀) t, t⟫)`. The information may
be singular here.

## Sources

- Lehmann & Casella (1998), §6.5; van der Vaart (1998), ch. 5; obtained from the multivariate CLT `ProbabilityTheory.tendstoInDistribution_inv_sqrt_smul_sum_sub` (Cramér–Wold reduction to the scalar CLT).
