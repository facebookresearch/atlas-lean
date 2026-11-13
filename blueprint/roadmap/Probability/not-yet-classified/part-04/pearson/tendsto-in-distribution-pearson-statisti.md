# Pearson's chi-square theorem

**Pearson's chi-square theorem** (simple null hypothesis, fixed cells). Let `X 0, X 1, …` be
i.i.d. observations in a finite set `ι` of `k ≥ 2` cells, with cell probabilities
`P(X 0 = i) = pᵢ > 0`. Then Pearson's statistic `∑ᵢ (Nᵢ - n pᵢ)² / (n pᵢ)` of the cell counts
`N = cellCount X n` converges in distribution to the chi-square law with `k - 1` degrees of
freedom.

The limit is derived from the singular Gaussian limit of the Pearson residuals
(`tendstoInDistribution_pearsonResidual`): the statistic is the squared norm of the residual
vector, and the squared norm of the projection of a standard Gaussian onto the rank-`(k - 1)`
hyperplane `(√p)ᗮ` is `χ²_{k-1}` by Cochran's theorem (`stdGaussian_map_norm_sq_starProjection`).
The assumption `k ≥ 2` is needed: for `k = 1` the statistic is identically `0` while
`chiSquareMeasure 0` is the zero measure.
