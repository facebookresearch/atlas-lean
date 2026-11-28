# The Cochran–Armitage statistic is N r²

With the subjects of the [Cochran–Armitage statistic](ca-stat.md), for every `N ∈ ℕ` and every
outcome `ω`, `T_N(ω) = N r²`, where `r²` is the squared sample correlation, in moment form, of the
genotype scores `x_m = G_m(ω)` and the [case indicators](case-ind.md) `c_m` of the subjects `m < N`:
with `mean(f) = (∑_{m<N} f_m) / N`,
`r² = (mean(x c) − mean(c) mean(x))² / ((mean(c²) − mean(c)²)(mean(x²) − mean(x)²))`. With the
convention `x / 0 = 0`, `r² = 0` when a sample variance vanishes and for `N = 0`, and both sides are
then `0`.
