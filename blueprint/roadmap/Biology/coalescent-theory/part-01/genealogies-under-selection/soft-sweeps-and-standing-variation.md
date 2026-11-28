# Genealogies of soft sweeps

In a soft sweep, several copies of the beneficial allele with independent origins contribute to its fixation.

For adaptation from recurrent mutation, Pennings and Hermisson (2006, Soft sweeps III, Model and Analytical Derivations) describe a sample taken directly after fixation by a structured coalescent in the growing beneficial and shrinking ancestral parts of the population: lineages at the selected site coalesce or escape the beneficial part by a back-in-time mutation, and at a linked neutral locus also by recombination. The Ewens law of the partition of a sample of size $n$ into ancestral haplotypes, one per independent origin (their Soft sweeps II), is stated in [beta-binomial estimation of the beneficial mutation supply from soft sweeps](../../../detecting-selection/genealogy-based-inference-of-selection/soft-sweeps-from-recurrent-mutation/beta-binomial-estimation-of-the-beneficial-mutation-supply.md) and is not restated here; in Pennings and Hermisson's notation its parameter is $\Theta_b = 2N_e u_b$, where $u_b$ is the mutation rate to the beneficial allele. Combining the haplotype partition with a neutral coalescent for the ancestral haplotypes before the selective phase gives the spectrum of ancestral polymorphisms; conditionally on $k$ haplotypes, singletons and $(n - 1)$-tons occur in the ratio $(k - 1) : 1$, so the spectrum is symmetric for $k = 2$.

For adaptation from standing variation, Hermisson and Pennings (2005) approximate the number of independent copies present at the environmental change that go on to fix by a Poisson law with mean $\lambda = \Theta_u\log(1 + R_\alpha)$, obtained by equating $1 - e^{-\lambda}$ with their fixation probability from the standing variation, where $\Theta_u = 4N_e u$ and $R_\alpha = 2hs_b/(2h's_d + 1/(2N_e))$ is the relative selective advantage. The probability that more than one independent copy fixes, given fixation, is then $1 - \lambda e^{-\lambda}/(1 - e^{-\lambda})$ (their Equation 20, derived here from the Poisson law), which vanishes as $\Theta_u \to 0$.

## Depends on

- [Ewens sampling formula](../../../population-genetics/ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)
- [Law of the number of alleles](../../../detecting-selection/ewens-watterson-test/num-alleles-prob-eq.md)
- [Beta-binomial estimation of the beneficial mutation supply from soft sweeps](../../../detecting-selection/genealogy-based-inference-of-selection/soft-sweeps-from-recurrent-mutation/beta-binomial-estimation-of-the-beneficial-mutation-supply.md)

## Expansion

1. The recurrent-mutation model, the selective phase, and the structured coalescent in the beneficial and ancestral parts with escape by mutation and by recombination.
2. The spectrum of ancestral polymorphisms, and the $(k - 1) : 1$ ratio of singletons to $(n - 1)$-tons.
3. The standing-variation model, the Poisson approximation with mean $\Theta_u\log(1 + R_\alpha)$, and the probability of fixation of multiple independent copies (Equation 20), with its range of validity ($\alpha_d \ge 10$).

## Sources

- P. S. Pennings and J. Hermisson, Soft sweeps III: the signature of positive selection from recurrent mutation, PLoS Genet. 2 (2006), e186, Model and Analytical Derivations. <https://doi.org/10.1371/journal.pgen.0020186>
- J. Hermisson and P. S. Pennings, Soft sweeps: molecular population genetics of adaptation from standing genetic variation, Genetics 169 (2005), 2335–2352, Equations 8 and 20 and the surrounding text. <https://doi.org/10.1534/genetics.104.036947>
