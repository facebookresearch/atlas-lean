# Pearson's limit theorem for the asymptotic HWE test of this file

For i.i.d. genotypes in
Hardy–Weinberg proportions at a polymorphic allele frequency `0 < p < 1`, the statistic
`hweChiSqOfHet` behind `asymptoticHWEPValue`, evaluated at the observed sample size, allele count
and heterozygote count, converges in distribution to `χ²₁`. This is
`PearsonLimit.tendstoInDistribution_hweStat` transported along
`hweChiSqOfHet_eq_hweStat_cellCount`; the sparse counterexamples above show that the limit says
nothing about a fixed small sample.
