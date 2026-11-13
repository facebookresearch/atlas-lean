# The oracle statistic is asymptotically `χ²₁`

With the means `μ_A, μ_B` and variances
`Var A, Var B` known instead of fitted, `(N^{-1/2} ∑ (A - μ_A)(B - μ_B))² / (Var A · Var B)`
converges in distribution to `χ²₁`: the same limit as the fitted statistic of
`tendstoInDistribution_mul_sampleCorrSq`, so fitting the nuisance parameters costs the
contrast no degree of freedom.
