# Beta-binomial estimation of the beneficial mutation supply from soft sweeps

Suppose two distinct point mutations (alleles $1$ and $2$) produce the same beneficial phenotype, each arising at the same rate $\mu$ per genome per generation in a population of effective size $N_e$, and let $\theta = 2N_e\mu$; following the source, $\theta/2$ is the total population-wide beneficial mutation rate (the supply). After the beneficial phenotype has swept to fixation, the following hold approximately. They are the strong-selection approximations of the soft-sweep theory the source relies on (Pennings and Hermisson 2006): selection on the beneficial phenotype is strong ($N_e s \gg 1$, with $s$ its selective advantage) and the sample is small compared with the population. They are not exact identities for a finite population.

1. **Number of origins.** The partition of a sample of $n$ beneficial sequences by mutational origin is approximately distributed by Ewens' sampling formula with parameter $\theta$; in particular the probability that all $n$ sampled beneficial sequences descend from a single origin (a hard sweep in the sample) is approximately

$$\prod_{i=1}^{n-1} \frac{i}{i + \theta} = \frac{\Gamma(n)\,\Gamma(1 + \theta)}{\Gamma(n + \theta)} .$$

2. **Allele frequency.** The frequency $X$ of allele $1$ among beneficial copies is approximately $\mathrm{Beta}(\theta/2, \theta/2)$ distributed.

If in population $i$ ($i = 1, \dots, P$) a sample of $n_i$ beneficial sequences contains $k_i$ copies of allele $1$, with $k_i \mid X_i \sim \mathrm{Binomial}(n_i, X_i)$ independently, the approximate likelihood under this model (the source's Equation (1)) is the product of beta-binomial probabilities

$$L(\theta) = \prod_{i=1}^{P} \binom{n_i}{k_i} \frac{B(k_i + \theta/2,\, n_i - k_i + \theta/2)}{B(\theta/2, \theta/2)},$$

where $B$ is the beta function. Maximizing $L$ gives $\hat\theta$, the estimated supply is $\hat\theta/2$, and the effective size relevant for adaptation is estimated as $\hat N_e = \hat\theta/(2\mu)$. A sample containing both alleles proves a soft sweep, whatever the approximation (each allele needs its own mutation); a sample with one allele is compatible with either.

## Depends on

- [Ewens sampling formula](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)

## Expansion

Tracing the beneficial lineages backwards during the sweep, each lineage either coalesces with another beneficial lineage or reaches a mutational origin, and under strong selection the competition between these events has, to leading order, the same Hoppe-urn structure as the infinite-alleles coalescent, with mutation parameter $\theta$; this is why the Ewens and beta laws are approximations rather than exact laws. Labelling each origin independently as allele $1$ or $2$ with probability $1/2$ splits the Ewens (Dirichlet) frequencies into a $\mathrm{Beta}(\theta/2, \theta/2)$ fraction of allele $1$; integrating the binomial against this law gives the beta-binomial factor. In the source's simulations (its Figure S4) the number of origins did not depend on whether the beneficial mutations were standing variation or arose after the environmental change. In within-patient HIV data the source exploits that reverse-transcriptase codon 103 can mutate from AAA (lysine) to either AAC or AAT (asparagine, drug resistant): 7 of 17 populations carried both codons after the sweep. The fit gives $\hat\theta \approx 0.62$, an estimated supply $\hat\theta/2 \approx 0.31$ new resistance mutations per generation, and, with $\mu \approx 2 \times 10^{-6}$, an effective size $\hat\theta/(2\mu)$ around $1.5 \times 10^5$, far below the number of infected cells and far above estimates from synonymous diversity.

## Sources

- P. S. Pennings, S. Kryazhimskiy and J. Wakeley, "Loss and recovery of genetic diversity in adapting populations of HIV", *PLoS Genetics* 10 (2014), e1004000, Equation (1) and Methods section "Estimating the supply rate of resistance mutations", <https://doi.org/10.1371/journal.pgen.1004000> (PMC3900388).
- P. S. Pennings and J. Hermisson, "Soft sweeps II: molecular population genetics of adaptation from recurrent mutation or migration", *Molecular Biology and Evolution* 23 (2006), 1076–1084, <https://doi.org/10.1093/molbev/msj117>: the strong-selection Ewens approximation for the number of origins in a sample, cited by the source (its reference 4) for the beta law and the number of origins.
