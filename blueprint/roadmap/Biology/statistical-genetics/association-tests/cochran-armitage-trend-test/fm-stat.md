# Cochran–Armitage statistic of a fixed-margin design

For `R, N ∈ ℕ` and genotype classes `g_k ∈ {0, 1, 2}`, the subjects `0, …, R − 1` are the cases and
`R, …, N − 1` the controls. The statistic `T(R, N, g)` is the
[trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md) of the `2 × 3`
table with case counts `rᵢ = #{k < R : g_k = i}` and control counts
`sᵢ = #{k : R ≤ k < N, g_k = i}`: `T = N' U² / (R' S' (N' ∑ᵢ i² nᵢ − (∑ᵢ i nᵢ)²))` with
`R' = ∑ᵢ rᵢ`, `S' = ∑ᵢ sᵢ`, `nᵢ = rᵢ + sᵢ`, `N' = R' + S'` and `U = ∑ᵢ i (rᵢ S' − sᵢ R')`. For
`R ≤ N`, `R' = R`, `S' = N − R` and `N' = N`. With the convention `x / 0 = 0`, `T = 0` when `R = 0`,
when `R ≥ N` (no controls) and when all subjects of the table are in one genotype class; the
intended domain is `0 < R < N`.
