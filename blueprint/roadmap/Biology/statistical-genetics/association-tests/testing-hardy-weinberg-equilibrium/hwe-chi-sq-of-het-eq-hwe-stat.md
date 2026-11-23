# The heterozygote-count statistic is the genotype-table statistic

For a genotype table
with `n₀` individuals of class `0` (`BB`), `n₁` of class `1` (`AB`) and `n₂` of class `2` (`AA`),
`hweChiSqOfHet` at the sample size `N = n₀ + n₁ + n₂`, the allele count `n_A = n₁ + 2 n₂` and the
heterozygote count `n₁` is Pearson's fitted statistic `hweStat` of the table: the floor divisions
and truncated subtractions in `hweChiSqOfHet` are exact on every realizable table.
