# Weir–Cockerham estimator of $F_{ST}$ from allele samples as a ratio of unbiased estimators

Sample $n_i \ge 1$ alleles from each of $r \ge 2$ populations, with $n_i \ge 2$ for at least one $i$, let $\tilde p_{iu}$ be the sample frequency of allele $A_u$ in population $i$ and $\bar p_u$ the sample-size-weighted average, and suppose that within populations the sample frequencies have multinomial moments, and among populations the frequencies $p_{iu}$ have mean $p_u$ and variance $p_u(1 - p_u)\theta$ with no coancestry between populations. With the mean squares

$$\mathrm{MSP}_u = \frac{1}{r - 1}\sum_{i=1}^r n_i (\tilde p_{iu} - \bar p_u)^2, \qquad \mathrm{MSG}_u = \frac{1}{\sum_i (n_i - 1)} \sum_{i=1}^r n_i\, \tilde p_{iu}(1 - \tilde p_{iu}),$$

one has $E(\mathrm{MSP}_u) = \pi_u[(1 - \theta) + n_c\theta]$ and $E(\mathrm{MSG}_u) = \pi_u(1 - \theta)$ with $\pi_u = p_u(1 - p_u)$ and $n_c = \frac{1}{r - 1}\bigl(\sum_i n_i - \sum_i n_i^2 / \sum_i n_i\bigr)$ (Weir and Hill 2002, restating Weir and Cockerham 1984). Hence $\mathrm{MSP}_u - \mathrm{MSG}_u$ and $\mathrm{MSP}_u + (n_c - 1)\mathrm{MSG}_u$ are unbiased for $n_c \pi_u \theta$ and $n_c \pi_u$, and the Weir–Cockerham moment estimator

$$\hat\theta = \frac{\sum_u (\mathrm{MSP}_u - \mathrm{MSG}_u)}{\sum_u [\mathrm{MSP}_u + (n_c - 1)\mathrm{MSG}_u]},$$

with numerator and denominator summed over alleles (and over loci when $\theta$ is common to them), is a ratio of unbiased estimators of $\theta$ times a common factor and of that factor. It is defined only on samples whose observed denominator is positive: if every population sample is monomorphic for the same allele, then $\tilde p_{iu} = \bar p_u \in \{0, 1\}$ for all $i$ and $u$, every mean square vanishes, and $\hat\theta = 0/0$; the identities for the expectations of the numerator and denominator need no such restriction. Where it is defined, it is unbiased only to the extent that the expectation of the ratio equals the ratio of the expectations.

This is the allele-level sampling model, with no individuals or genotypes. The diploid version, in which the genotype-level statistics $a$, $b$, $c$ are unbiased for the [variance components](weir-cockerham-variance-components.md) and $\hat\theta = \sum a / \sum (a + b + c)$, is the [Weir–Cockerham estimator of $\theta$](weir-cockerham-theta-estimator.md).

## Expansion

1. The model: multinomial sampling within populations and the among-population moments that introduce $\theta$.
2. The expectations of $\mathrm{MSP}_u$ and $\mathrm{MSG}_u$ under the general model with population-specific $\theta_i$ and between-population $\theta_{ii'}$, and their specialization to equal $\theta$ and zero $\theta_{ii'}$.
3. Unbiasedness of the numerator and denominator, the combination over alleles and loci, and the event of a positive observed denominator on which the ratio is defined.
4. Consistency of the ratio estimator as the number of loci grows, its bias, and its relation to the [nonnegativity of the fixation index](../../../Biology/population-structure/patterson-s-f-statistics/fst-nonneg.md), as separate statements.

## Sources

- B. S. Weir and W. G. Hill, Estimating F-statistics, Annu. Rev. Genet. 36 (2002), 721–750, section on moment estimators. <https://doi.org/10.1146/annurev.genet.36.050802.093940>
- Original result: B. S. Weir and C. C. Cockerham, Estimating F-statistics for the analysis of population structure, Evolution 38 (1984), 1358–1370. <https://doi.org/10.2307/2408641> The mean squares, their expectations and the ratio estimator follow Weir and Hill (2002).
