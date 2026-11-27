# Heterozygosity relaxation statistic

**Definition.** In a collection of diploid genomes, tile the genome into windows and let $S$ be the set of window midpoints whose local heterozygosity lies in a narrow range (for example $5$–$10$ heterozygous sites per $100$ kb). For genetic distance $d$ (in Morgans), the **heterozygosity relaxation statistic** $H_S(d)$ is the average heterozygosity (fraction of heterozygous sites) at genetic distance $d$ from the points of $S$. It starts at $H_S(0)$ and relaxes toward the genome-wide mean heterozygosity $\bar H$ as $d$ grows.

**Scaling principle.** At a site where the two haplotypes of an individual have time to most recent common ancestor $T$ (generations), the expected heterozygosity is $2\mu T$ for per-base mutation rate $\mu$. Moving genetic distance $d$ away, the two lineages are still unbroken by recombination with probability $e^{-2dT}$ (recombination along a total branch length $2T$), so the relaxation of $H_S(d)$ happens on the genetic-distance scale $d \sim 1/(2T)$. Since conditioning on $H_S(0)$ fixes the starting TMRCA at about $T \approx H_S(0)/(2\mu)$, the relaxation length scale is about $\mu / H_S(0)$: for fixed $H_S(0)$, a **larger $\mu$ means younger starting blocks, fewer recombinations per unit of genetic distance and a slower relaxation**. The curve $d \mapsto H_S(d)$ therefore identifies $\mu$ relative to the recombination rate, with the genetic map providing the calibration.

**Estimator.** Because the TMRCAs on the two sides of a recombination are dependent (both exceed the recombination time, and the ancestral recombination graph allows the split lineages to re-coalesce), $H_S(d)$ has no closed form. Instead, simulate genomes under the coalescent with recombination with the population-size history inferred by PSMC (keeping the diversity $\theta = 4N\mu$ and setting the scaled recombination rate to $\theta r/\mu$), using a genetic map perturbed to match the real map's error, at several trial rates $\mu$; interpolate the observed $H_S(d)$ between the simulated curves and fit $\mu$ by variance-weighted least squares. The raw estimate is then corrected for false heterozygous calls (estimated from the CpG fraction of heterozygous sites), for non-crossover gene conversion, and for base composition.

## Depends on

- [Expected differences of a pair are θ times its mean coalescence time](../../../coalescent-theory/pairwise-differences-under-poisson-mutation/integral-pair-diff-of-mutation.md)
- [Pairwise sequentially Markov coalescents SMC and SMC′](../../../coalescent-theory/two-locus-coalescent/sequentially-markov-coalescent-smc-smc-pairwise.md)
- [Haldane's map function](../../../population-genetics/linkage-disequilibrium-and-haldane-s-map-functio/haldane.md)
- [Coalescent with recombination: ancestral-material state space and generator](../../../coalescent-theory/two-locus-coalescent/coalescent-with-recombination-ancestral-material.md)
- [Stationary-kernel discretization for pairwise SMC hidden Markov models](../../../../ComputerScience/machine-learning/probabilistic-graphical-models/baum-welch-algorithm/pairwise-smc-hmm-psmc-discretized-tmrca-hidden-s.md)

## Expansion

Applied to eight non-African genomes with starting points of $5$–$10$ heterozygous sites per $100$ kb ($H_S(0) \approx 7.4 \times 10^{-5}$, TMRCAs of roughly $1{,}500$–$3{,}100$ generations), the procedure gives $\mu = 1.61 \pm 0.13 \times 10^{-8}$ per base per generation, between pedigree-based and phylogenetic estimates. Low starting heterozygosity is chosen because the relaxation is then slower and of larger amplitude, hence less sensitive to map error. Map error is modelled by drawing the true genetic length $Z$ of each map interval of observed genetic length $g$ and physical length $p$ as $Z \sim \mathrm{Gamma}(\alpha \gamma (g + \pi p), \alpha)$, a gamma error model with a pseudo-count $\pi$ that keeps zero-length intervals from staying exactly zero and a constant $\gamma < 1$ that preserves total map length; $1/\alpha$ is the genetic length at which the map's coefficient of variation is $1$.

## Sources

- M. Lipson, P.-R. Loh, S. Sankararaman, N. Patterson, B. Berger and D. Reich, "Calibrating the human mutation rate via ancestral recombination density in diploid genomes", PLoS Genetics 11 (2015), e1005550, Results ("Overview of methods", "Estimates for Europeans and East Asians") and Methods ("Definition of the statistic $H_S(d)$", "Inference strategy", "Population size history", "Genetic map error"), <https://doi.org/10.1371/journal.pgen.1005550>, PMCID PMC4642934.
