# In Chi Sq Regime

The large-sample regime for `N` individuals with genotype table `n`: every expected genotype
count `N * hweProb (alleleFreqHat n) i`, the denominator of `hweStat N n`, is at least `c`.
Pearson's limit theorem `PearsonLimit.tendstoInDistribution_hweStat` fixes the allele frequency
in `(0, 1)` and lets `N → ∞`, which sends every expected count to infinity; Cochran's
finite-sample rule takes `c = 5`.
