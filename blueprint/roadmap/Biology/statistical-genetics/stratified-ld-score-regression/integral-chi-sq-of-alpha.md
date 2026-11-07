# Frequency-dependent architecture

**Frequency-dependent architecture** (the α model of Schoech et al. 2019): if the per-allele
effect variance of marker `k` with allele frequency `p_k` is proportional to `[p_k (1 - p_k)]^α`,
the variance of the effect of the standardized genotype is `σ²_k = c [p_k (1 - p_k)]^(1 + α)`,
and then, for a standardized genotype matrix and `N ≠ 0`,
`𝔼[χ² j] = N c ∑_k [p_k (1 - p_k)]^(1 + α) r_jk² + σ²_e`. (The real power is meaningful for
`0 < p_k < 1`.)
