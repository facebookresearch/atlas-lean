# With `p` known, the Hardy–Weinberg Pearson statistic is asymptotically `χ²₂`

Under the
hypotheses of `tendstoInDistribution_hweStat`, Pearson's statistic against the *true*
Hardy–Weinberg proportions, `∑ᵢ (nᵢ - N hweProb p i)² / (N hweProb p i)`, converges in
distribution to `χ²₂` (`3` cells, `3 - 1` degrees of freedom; the canonical simple-null
`ProbabilityTheory.tendstoInDistribution_pearsonStatistic`). Estimating `p` by `p̂` lowers the
limit to `χ²₁`.
