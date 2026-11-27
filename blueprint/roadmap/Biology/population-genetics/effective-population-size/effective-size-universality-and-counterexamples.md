# Coalescent effective size and failure of binary universality

For a Cannings model with $N \ge 2$ haploid individuals and exchangeable offspring numbers $\nu_1, \dots, \nu_N$, the probability that two lineages coalesce in one generation is

$$c_N = \frac{E[\nu_1(\nu_1 - 1)]}{N - 1}$$

(Wakeley, King, Low and Ramachandran 2012, equation (1)). When $c_N > 0$ the coalescent time unit is $1/c_N$ generations; if $c_N = 0$, as when every parent has exactly one child, lineages never coalesce and neither the time unit nor the effective size below is defined. The coalescent effective size is the size of the Wright–Fisher population with the same pair coalescence probability, $N_e = 1/c_N$ in haploid units, for $c_N > 0$. It is a scaling factor of the coalescent time and not a census size (Nordborg 2001; Sjödin, Kaj, Krone, Lascoux and Nordborg 2005, Introduction and section "The coalescent"): it is a function of the demographic parameters, such as the harmonic mean of rapidly fluctuating sizes or a function of the deme sizes and migration under fast migration (Sjödin et al. 2005, sections "Fluctuating population size" and "Structured populations"), and it need not equal the total population size; under strong but non-conservative migration, for instance, a subdivided population behaves as an unstructured one with lowered variance effective size (Nordborg 1999, Section 5.1, pp. 74–75). The scaling describes the genealogy only when the limit is Kingman's coalescent. Populations that are subdivided or vary in size cannot in general be modelled by a linear change of the coalescent time scale: size fluctuations on the coalescent time scale give Kingman's coalescent on a nonlinear random clock, and migration on that scale gives a structured coalescent, neither with an effective size (Sjödin et al. 2005, sections "Fluctuating population size" and "Structured populations", and Discussion; Nordborg 1999, Section 5.1, pp. 74–75; Rosenberg and Nordborg 2002, p. 383, where structure and size fluctuation change the shape of genealogies and not only the rate of coalescence), and in models with highly skewed offspring numbers the genealogy converges to a coalescent with multiple mergers, which has no effective population size in the usual sense (Eldon and Wakeley 2006, Introduction and Discussion). So the binary Kingman limit of large populations is not universal, and $1/c_N$ alone does not determine the genealogy.

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
- M. Nordborg, Coalescent theory, in D. J. Balding, M. Bishop and C. Cannings (eds.), *Handbook of Statistical Genetics*, Wiley, Chichester, 2001, pp. 179–212 (general reference for effective population size).
- P. Sjödin, I. Kaj, S. Krone, M. Lascoux and M. Nordborg, On the meaning and existence of an effective population size, Genetics 169 (2005), 1061–1070, Introduction, sections "The coalescent", "Fluctuating population size" and "Structured populations", and Discussion. <https://pmc.ncbi.nlm.nih.gov/articles/PMC1449138/>. <https://doi.org/10.1534/genetics.104.026799>
- M. Nordborg, The coalescent with partial selfing and balancing selection: an application of structured coalescent processes, in *Statistics in Molecular Biology and Genetics*, IMS Lecture Notes–Monograph Series 33 (1999), 56–76, Section 5.1, pp. 74–75. Open access at Project Euclid. <https://doi.org/10.1214/lnms/1215455547>
- N. A. Rosenberg and M. Nordborg, Genealogical trees, coalescent theory and the analysis of genetic polymorphisms, Nat. Rev. Genet. 3 (2002), 380–390, p. 383. <https://doi.org/10.1038/nrg795>
- B. Eldon and J. Wakeley, Coalescent processes when the distribution of offspring number among individuals is highly skewed, Genetics 172 (2006), 2621–2633, Introduction and Discussion. <https://doi.org/10.1534/genetics.105.052175>
