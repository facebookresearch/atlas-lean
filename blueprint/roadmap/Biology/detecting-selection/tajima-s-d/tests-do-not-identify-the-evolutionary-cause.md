# Neutrality tests do not identify the cause of a rejection

Neutrality statistics built from the site-frequency spectrum, such as Tajima's $D$, are calibrated under the neutral constant-size panmictic model, and neutral models with changing size or with population structure move them as well. Tajima (1989, Abstract) computes the expected number of segregating sites $S$ and the expected mean number of pairwise differences $\pi$ for a population that is not at equilibrium, and finds that after a drastic change in size $S$ depends more strongly on the current size and $\pi$ more strongly on the original size, and that a bottleneck affects $\pi$ more strongly than $S$. Since the numerator of Tajima's $D$ is $\pi - S/a_1$, with mean zero at constant size, a change of size alone shifts its expectation away from zero, with a sign that depends on the history. Population structure has the same effect: in the $n$-island model with constant total size, the inverse instantaneous coalescence rate of two genes from one deme increases backward in time from the size of one deme to a larger value, the signature that a size-change model reads as a population decline (Mazet, Rodríguez, Grusea, Boitard and Chikhi 2016, Figure 1). A rejection of the constant-size neutral model is therefore evidence against that model as a whole, not specifically evidence of selection.

## Depends on

- [Tajima's numerator has mean zero](../../../Biology/coalescent-theory/segregating-sites-and-pairwise-differences/integral-tajima-numerator.md)
- [Expected site frequency spectrum under variable population size](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/variable-sfs.md)
- [Tajima's $\theta_\pi$ in site frequency spectrum form](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/theta-pi.md)
- [Tajima's D can have positive mean while its numerator has mean zero](../../../Biology/detecting-selection/mean-and-asymptotic-normality-of-tajima-s-d/exists-integral-tajima-d-ne.md)
- [Distribution of the pairwise coalescence time in the island model](../../../Biology/coalescent-theory/structured-coalescent/island-coalescence-time-distribution.md)
- [Inverse instantaneous coalescence rate of a pairwise coalescence time](../../coalescent-theory/inverse-instantaneous-coalescence-rate/iicr-of-a-pairwise-coalescence-time.md)

## Expansion

1. The expectation of the numerator of Tajima's $D$ under a general size history, from the expected spectrum under variable size.
2. A growth history and a bottleneck history with explicitly computed expectations of the numerator of opposite signs.
3. A structured model with constant deme sizes and a computed nonzero expectation of the numerator for a sample from one deme.
4. The inverse instantaneous coalescence rate of the island model, which varies in time although every deme has constant size.

## Sources

- F. Tajima, The effect of change in population size on DNA polymorphism, Genetics 123 (1989), 597–601, Abstract. <https://doi.org/10.1093/genetics/123.3.597>
- O. Mazet, W. Rodríguez, S. Grusea, S. Boitard and L. Chikhi, On the importance of being structured: instantaneous coalescence rates and human evolution—lessons for ancestral population size inference?, Heredity 116 (2016), 362–371, section Linking population structure and population size change and Figure 1. <https://doi.org/10.1038/hdy.2015.104>
