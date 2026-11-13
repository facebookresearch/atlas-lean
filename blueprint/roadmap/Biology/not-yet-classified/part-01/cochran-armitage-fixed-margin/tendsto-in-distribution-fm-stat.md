# The Cochran–Armitage test under the fixed-margin case–control design is asymptotically `χ²₁`

**The Cochran–Armitage test under the fixed-margin case–control design is asymptotically
`χ²₁`.**

For each sample size `N` the design has `R N ≤ N` cases (subjects `k < R N`) and `N - R N`
controls (subjects `R N ≤ k < N`), with genotype classes `G N k ∈ {0, 1, 2}` independent within
the design; cases have genotype law `πcase` and controls `πctrl` (product-binomial sampling: the
numbers of cases and controls are fixed, not random). Under the null `πcase = πctrl`, if the
genotype score has positive variance and both the number of cases and the number of controls
tend to infinity, then the trend statistic `fmStat (R N) N` converges in distribution to `χ²₁`.

No condition on the case fraction `R N / N` is needed: it may oscillate or tend to `0` or `1`.

Measurability `Measurable (G N k)` is assumed for every `k`, including the entries `k ≥ N` that
the statistic never reads; a caller can set those entries to a constant.
