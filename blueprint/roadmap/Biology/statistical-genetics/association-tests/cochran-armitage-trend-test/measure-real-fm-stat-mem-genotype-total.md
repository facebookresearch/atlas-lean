# Exact conditional null law of the Cochran–Armitage statistic

Let the genotype classes be `0, 1, 2`, `P` a probability measure, `R, S ∈ ℕ`, and
`G_0, …, G_{R+S−1}` random genotype classes that are independent under `P`: the `R` cases `G_k`,
`k < R`, with law `π_case`, and the `S` controls `G_k`, `R ≤ k < R + S`, with law `π_ctrl`. Suppose
the null hypothesis `π_case = π_ctrl`. Then for every set `A` of real numbers, measurable or not,
and every margin `n`,

`P(T_fm ∈ A and genotype margin = n) = (∑ H(R; n, r)) · P(genotype margin = n)`,

where `T_fm` is the [fixed-margin statistic](fm-stat.md) with `R` cases among `R + S` subjects, the
sum runs over the count vectors `r` with `rᵢ ≤ nᵢ` for every `i` whose
[trend statistic](../../genomic-prediction-from-summary-statistics/trend-stat.md) `T(r, n − r)` lies
in `A`, and `H` is the [multivariate hypergeometric mass](mv-hypergeometric-real.md). Given a margin
of positive probability, the statistic is therefore distributed as `T(r, n − r)` with `r`
multivariate hypergeometric, the permutation distribution behind the exact Cochran–Armitage test,
whatever the common genotype law.

## Sources

- N. Mantel, *Chi-square tests with one degree of freedom; extensions of the Mantel–Haenszel
  procedure*, J. Amer. Statist. Assoc. 58 (1963), 690–700.
