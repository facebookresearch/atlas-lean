# The coalescent with partial self-fertilization

In a population of $N$ diploid hermaphrodites in which each fertilization occurs by selfing with probability $S$ and by outcrossing otherwise, Nordborg (2001, section "Hermaphrodites") derives the genealogy of a sample by a separation of time scales. With time in units of $2N$ generations, each pair of lineages enters a common individual at rate $2$; half of these events are real coalescences, and otherwise the two lineages occupy distinct genes of one individual. From there they coalesce before separating into different individuals with probability

$$F = \frac{S/2}{S/2 + 1 - S} = \frac{S}{2 - S},$$

the equilibrium inbreeding coefficient (equation (13)), so the coalescence rate per pair is $1 + F$ and all states with two lineages in one individual are instantaneous on this time scale. The genealogy of a random sample of gene copies is therefore Kingman's coalescent with time measured in units of $2N_e = 2N/(1 + F)$ generations (equation (14); compare the [effective size of a finite population with partial selfing](../../population-genetics/effective-population-size/effective-size-under-partial-selfing.md)). The two copies sampled from one individual coalesce instantaneously with probability $F$, so a sample of $2n$ copies from $n$ individuals starts with $2n - X$ distinct lineages, $X$ binomial with parameters $n$ and $F$. With recombination, the ancestral recombination graph of a partially selfing population reduces to the standard graph with the effective recombination rate $\rho_e = \rho(1 - F)$ (Nordborg 2001, section on the ancestral recombination graph; Nordborg 2000).

## Depends on

- [Inbreeding coefficient under partial self-fertilization](../../../Biology/population-genetics/inbreeding-and-regular-systems-of-mating/inbreeding-under-partial-selfing.md)

## Expansion

1. The partial-selfing model and the two-lineage chain: lineages in distinct individuals, in one individual, or coalesced.
2. The fast phase within an individual: absorption probabilities $F$ and $1 - F$.
3. The separation-of-time-scales limit, giving Kingman's coalescent with pair rate $1 + F$ on the $2N$-generation scale.
4. The initial instantaneous coalescence of copies sampled from one individual, with the binomial number of merged pairs.
5. The ancestral recombination graph with selfing and the effective recombination rate $\rho(1 - F)$.

## Sources

- M. Nordborg, Coalescent theory, in *Handbook of Statistical Genetics*, Wiley, 2001 (preprint of March 2000), sections "Hermaphrodites" (equations (13), (14), Figure 8) and "The ancestral recombination graph".
- M. Nordborg, Linkage disequilibrium, gene trees and selfing: an ancestral recombination graph with partial self-fertilization, Genetics 154 (2000), 923–929, abstract. <https://doi.org/10.1093/genetics/154.2.923>
- M. Nordborg, Structured coalescent processes on different time scales, Genetics 146 (1997), 1501–1514, abstract. <https://doi.org/10.1093/genetics/146.4.1501>
- Original result: M. Möhle, A convergence theorem for Markov chains arising in population genetics and the coalescent with selfing, Adv. Appl. Probab. 30 (1998), 493–512. <https://doi.org/10.1239/aap/1035228080> The formal convergence statement is cited by Nordborg (2001), section "Hermaphrodites".
