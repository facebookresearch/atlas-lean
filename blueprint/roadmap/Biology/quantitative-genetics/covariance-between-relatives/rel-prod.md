# Mean product of genotypic values of two relatives

In a [single-locus model](locus-model.md) with frequencies $p$ and genotypic values $g$, and for real numbers $k_0, k_1, k_2$, put

$$E(k_0, k_1, k_2) = k_0 \sum_{a,b,c,d} p_a p_b p_c p_d\, g(a, b)\, g(c, d) + k_1 \sum_{a,b,c} p_a p_b p_c\, g(a, b)\, g(a, c) + k_2 \sum_{a,b} p_a p_b\, g(a, b)^2.$$

For IBD probabilities $k_i$ (the probability that two non-inbred relatives share $i$ alleles identical by descent, the non-shared alleles being independent draws from $p$), it is the mean product of their genotypic values.
