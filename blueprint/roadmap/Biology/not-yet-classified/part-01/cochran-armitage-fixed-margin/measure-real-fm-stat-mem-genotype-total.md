# Exact conditional null law of the Cochran–Armitage statistic

Under the fixed-margin
null of `measureReal_caseCount_genotypeTotal`, conditional on the genotype margin `n`, the trend
statistic is distributed as `trendStat(r, n - r)` with `r` multivariate hypergeometric: for every
set `T` of values,
`P(fmStat ∈ T, margin = n) = (∑ {H(r ∣ n) : r ≤ n, trendStat(r, n - r) ∈ T}) · P(margin = n)`.
This is the permutation distribution behind the exact Cochran–Armitage test; it does not depend
on the common genotype law.
