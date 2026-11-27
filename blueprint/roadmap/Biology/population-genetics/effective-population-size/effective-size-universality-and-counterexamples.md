# Coalescent effective size and failure of binary universality

For a Cannings model with $N \ge 2$ haploid individuals and exchangeable offspring numbers $\nu_1, \dots, \nu_N$, the probability that two lineages coalesce in one generation is

$$c_N = \frac{E[\nu_1(\nu_1 - 1)]}{N - 1}$$

(Wakeley, King, Low and Ramachandran 2012, equation (1)). When $c_N > 0$ the coalescent time unit is $1/c_N$ generations; if $c_N = 0$, as when every parent has exactly one child, lineages never coalesce and neither the time unit nor the effective size below is defined. The coalescent effective size is the size of the Wright–Fisher population with the same pair coalescence probability, $N_e = 1/c_N$ in haploid units, for $c_N > 0$. It is a scaling factor of the coalescent time and not a census size: it is always a function of the demographic parameters, but it has no direct relation to the total population size, which may be smaller or much larger (Nordborg 2001, section on effective population size). The scaling describes the genealogy only when the limit is Kingman's coalescent. Populations that are subdivided or vary in size cannot in general be modelled by a linear change of the coalescent time scale (Nordborg 2001), and in models with highly skewed offspring numbers the genealogy converges to a coalescent with multiple mergers, which has no effective population size in the usual sense (Eldon and Wakeley 2006, Introduction and Discussion). So the binary Kingman limit of large populations is not universal, and $1/c_N$ alone does not determine the genealogy.

## Depends on

- [Möhle–Sagitov: genealogies converge to Kingman's in finite dimensions](../../../Biology/coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/tendsto-chain-fdd.md)
- [Explicit skew-offspring models and their Λ-coalescent limits](../../../Biology/coalescent-theory/multiple-merger-coalescents/coalescent-limits-of-cannings-models/explicit-skew-offspring-models.md)
- [Effective population size and the variance in family size](../../../Biology/population-genetics/effective-population-size/effective-size-and-variance-in-family-size.md)
- [Cannings model of a haploid population](../../coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md)
- [Pair-coalescence probability of a Cannings model](../../coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/pair-coalescence.md)

## Expansion

1. The pair coalescence probability $c_N$ of a Cannings model and, for $c_N > 0$, the coalescent effective size $1/c_N$, with its relation to the offspring variance at constant size.
2. The Kingman limit on the time scale $1/c_N$ under the Möhle–Sagitov conditions, where the coalescent effective size fully determines the genealogy.
3. Non-universality: explicit skew-offspring families whose limits have multiple mergers, so that no single effective size describes the genealogy.
4. Structured and fluctuating populations whose genealogies are not a linear time change of Kingman's coalescent.

## Sources

- J. Wakeley, L. King, B. S. Low and S. Ramachandran, Gene genealogies within a fixed pedigree, and the robustness of Kingman's coalescent, Genetics 190 (2012), 1433–1445, equation (1). <https://doi.org/10.1534/genetics.111.135574>
- M. Nordborg, Coalescent theory, in *Handbook of Statistical Genetics*, Wiley, 2001 (preprint of March 2000), section on effective population size.
- B. Eldon and J. Wakeley, Coalescent processes when the distribution of offspring number among individuals is highly skewed, Genetics 172 (2006), 2621–2633, Introduction and Discussion. <https://doi.org/10.1534/genetics.105.052175>
