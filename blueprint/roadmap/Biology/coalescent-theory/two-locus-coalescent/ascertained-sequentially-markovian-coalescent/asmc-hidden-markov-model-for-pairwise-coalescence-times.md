# ASMC hidden Markov model for pairwise coalescence times

Fix two haploid genomes (the *distinguished* pair), $n - 2$ further *undistinguished* haploid genomes from the same population, a piecewise-constant demographic history and a genetic map. Discretize time into $s$ intervals. The ascertained SMC (ASMC) is the hidden Markov model along the observed sites in which:

- **Hidden state** at a site: the interval containing the pair's time to most recent common ancestor (TMRCA) $\tau$.
- **Initial distribution and transitions**: the stationary law of the pairwise TMRCA and the transition probabilities between intervals given by the conditional Simonsen–Churchill (CSC) Markov approximation of the coalescent with recombination, which stays accurate for widely spaced markers.
- **Emission**: at a site where the distinguished pair carries $d \in \{0, 1, 2\}$ derived alleles and the undistinguished samples carry $u \in \{0, \dots, n-2\}$, the emission probability is

$$P(\mathrm{obs} \mid d + u) \times P(d, u \mid \tau),$$

where $P(d, u \mid \tau)$ is the conditioned sample frequency spectrum (CSFS) given the pair's TMRCA and $P(\mathrm{obs} \mid j)$ is the probability that a site with $j$ derived alleles in the sample is ascertained, estimated as the ratio of the empirical allele frequency spectrum of the data to the frequency spectrum expected under neutrality for the given demography.

Posterior TMRCA distributions are computed by the forward–backward algorithm. Under the CSC transition matrix $T$, each forward update $\alpha'_i = \sum_{k=1}^{s} \alpha_k T_{k,i}$ can be written as a linear combination of three terms that are each updated recursively in $O(1)$, so a forward or backward pass costs $O(sm)$ for $m$ observed sites instead of $O(s^2 m)$.

## Depends on

- [Pairwise sequentially Markov coalescents SMC and SMC′](../sequentially-markov-coalescent-smc-smc-pairwise.md)

## Expansion

The undistinguished samples enter only through allele counts, so their genealogy need not be tracked; they help because an allele's frequency carries information about its age and hence about whether the distinguished pair's lineages had already coalesced when it arose. Multiplying the CSFS term by the ascertainment probability, so that frequency classes the array over-represents carry proportionally more weight, is what lets the model run on arrays that over-represent common SNPs; the ratio of the empirical to the neutral spectrum estimates that multiplier, not its inverse. For sequence data, a run of $n$ monomorphic sites followed by a polymorphic one would require $\alpha (T E_0)^n T E_p$ with diagonal emission matrices $E_0$ (monomorphic) and $E_p$ (polymorphic); because $T$ is close to the identity over short genetic distances, the product is approximated by moving the powers of $T$ and $E_0$ apart, which reduces sequence-length dependence by two to three orders of magnitude. In simulations the posterior mean TMRCA correlated with the truth at $r^2 = 0.95$ on sequence data and $r^2 = 0.87$ at UK Biobank array density.

## Sources

- P. F. Palamara, J. Terhorst, Y. S. Song and A. L. Price, "High-throughput inference of pairwise coalescence times identifies signals of selection and enriched disease heritability", *Nature Genetics* 50 (2018), 1311–1317, Online Methods sections "ASMC model overview", "Emission model", "Transition model" and "Inference", <https://doi.org/10.1038/s41588-018-0177-x> (PMC6145075).
