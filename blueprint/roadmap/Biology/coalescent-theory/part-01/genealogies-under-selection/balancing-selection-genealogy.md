# Allelic genealogies under strong balancing selection

Takahata (1990, Abstract) considers alleles maintained by strong symmetric balancing selection, with $N$ the effective population size, $u$ the mutation rate to selected alleles per locus per generation and $s$ the selection coefficient, and sets $M = Nu$ and $S = 2Ns$. He shows that the genealogy of the distinct alleles (the allelic genealogy) has the same structure as the coalescent of a sample of neutral genes from a panmictic population at equilibrium, and differs from it only by a change of time scale, with approximate scaling factor

$$\sqrt{\frac{S}{2M}}\,\Bigl[\ln\frac{S}{16\pi M^2}\Bigr]^{-3/2}$$

relative to the neutral gene genealogy; the factor is large when $\sqrt{S/M} \ge 100$, and simulations support the approximation. Coalescent results for neutral genes, those of [Kingman's coalescent](../../partition-valued-kingman-coalescent/kingman-coalescent-on-n-as-a-time-indexed-cadlag.md) and its [holding times](../../kingman-s-coalescent-and-watterson-s-estimator/kingman-times.md), therefore apply to allelic lines after this rescaling. Combined with the trans-species evolution of the major histocompatibility complex polymorphism, for which balancing selection is believed to be responsible, Takahata uses the allelic genealogy to conclude that the number of breeding individuals in the human population could not have been as small as $50$ to $100$ at any time in its evolutionary history.

## Expansion

1. The model of strong symmetric balancing selection with mutation to new selected alleles, and the parameters $M = Nu$ and $S = 2Ns$.
2. The allelic genealogy and its approximation by a time-changed Kingman coalescent, with the scaling factor above and the regime $\sqrt{S/M} \ge 100$.
3. Linked neutral variation: the allelic classes as subpopulations exchanging lineages by recombination or mutation, and coalescence of lineages in different classes only after moving into a common class, as a separate statement.
4. Trans-species polymorphism: the probability that allelic lineages predate a speciation event under the rescaled coalescent.

## Sources

- N. Takahata, A simple genealogical structure of strongly balanced allelic lines and trans-species evolution of polymorphism, Proc. Natl. Acad. Sci. USA 87 (1990), 2419–2423, Abstract. <https://doi.org/10.1073/pnas.87.7.2419>
