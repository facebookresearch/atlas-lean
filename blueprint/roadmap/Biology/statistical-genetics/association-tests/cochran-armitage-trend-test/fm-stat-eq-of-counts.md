# The fixed-margin statistic from the case counts and the margin

For `R, S ∈ ℕ` and genotype classes `g_k ∈ {0, 1, 2}` whose [case counts](case-count-2.md) over
`k < R` are `r` and whose [genotype margin](genotype-total.md) over `k < R + S` is `n`, the
[fixed-margin statistic](fm-stat.md) with `R` cases among `R + S` subjects is the
[trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md) of the table with
case counts `rᵢ` and control counts `nᵢ − rᵢ`; these differences are nonnegative, since `rᵢ ≤ nᵢ`.
