# Trend statistic of a table with a single genotype class

For real vectors `r` and `s` indexed by the genotype classes `0, 1, 2` and a class `g` with
`rᵢ = sᵢ = 0` for every `i ≠ g`, the
[trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md) of the table is
`0`: with `nᵢ = rᵢ + sᵢ` and `N = ∑ᵢ nᵢ`, the variance factor `N ∑ᵢ i² nᵢ − (∑ᵢ i nᵢ)²` of its
denominator vanishes, and `x / 0 = 0`. The genotype score then has zero sample variance and the
classical statistic is undefined.
