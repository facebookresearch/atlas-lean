# Trend statistic of a table without controls

For real vectors `r` and `s` indexed by the genotype classes `0, 1, 2` with `∑ᵢ sᵢ = 0`, the
[trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md) of the table with
case counts `r` and control counts `s` is `0`: the factor `S = ∑ᵢ sᵢ` of its denominator vanishes,
and `x / 0 = 0`. For counts, `∑ᵢ sᵢ = 0` means that the table has no controls; the classical
statistic is undefined there.
