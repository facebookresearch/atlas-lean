# Sparse-count statistic

With two `A` alleles carried by a single `AA` homozygote among
`m + 1` individuals (`m ≥ 1`), Pearson's statistic is `X² = m + 1`: it grows linearly in the
sample size, so its `χ²₁` p-value decays like `e^{-(m+1)/2}` (`chiSqOneTail_toReal_le`), while for
`m = 9` the configuration has Levene probability `1/19` (`leveneProb_sparse_zero`).
