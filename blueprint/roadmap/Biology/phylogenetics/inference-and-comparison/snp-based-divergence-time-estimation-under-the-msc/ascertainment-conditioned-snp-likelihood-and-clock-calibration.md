# Ascertainment-conditioned SNP likelihood and strict-clock calibration

Let a model with parameters $\psi$ (species tree with divergence times, population-size parameters $\theta$, mutation model) assign probabilities $P(x \mid \psi)$ to the site patterns $x$ of unlinked biallelic markers, and let $\mathcal{C}$ be the set of patterns that are constant across all sampled individuals. If constant sites have been removed from the data, each retained site has the conditional likelihood

$$P(x \mid \psi, \text{variable}) = \frac{P(x \mid \psi)}{1 - \sum_{c \in \mathcal{C}} P(c \mid \psi)},$$

and the likelihood of $S$ independent SNPs is $\prod_{s=1}^{S} P(x_s \mid \psi)\, \bigl(1 - \sum_{c \in \mathcal{C}} P(c \mid \psi)\bigr)^{-S}$. To estimate absolute divergence times, the branch lengths in expected substitutions are divided by a strict-clock rate $\kappa$ whose prior is the improper scale-invariant density $p(\kappa) \propto 1/\kappa$, and $\kappa$ is identified by an age constraint on one node of the species tree. Given the per-generation mutation rate $\mu_g$ (clock rate divided by generations per unit time), the effective population size is recovered as $N_e = \theta / (4 \mu_g)$.

## Depends on

- [Rooted binary species tree with branch lengths](../../../coalescent-theory/multispecies-coalescent/species-tree.md)

## Expansion

Removing constant sites is a selection event, and conditioning on it divides each pattern probability by the probability of being selected; ignoring it treats an excess of variable sites as evidence of high mutation rates or large populations. The prior $1/\kappa$ is invariant under rescaling of time units, because $\log \kappa$ is uniform, but being improper it cannot be used for marginal-likelihood model comparison. In simulations of 20-species trees with SNPs only, the conditioned likelihood recovered population sizes correctly (95% of 95% HPD intervals contained the truth) although the clock rate and $\theta$ were each underestimated by a factor of about three, whereas omitting the correction overestimated both by more than an order of magnitude and underestimated population sizes. Compared with concatenation, which ignores incomplete lineage sorting, the multispecies coalescent estimates were equally good for old nodes but avoided the overestimation of young node ages that concatenation showed, an overestimation that grew with population size. Applied to sea catfishes, the method supported a Miocene closure of the Isthmus of Panama.

## Sources

- Stange M, Sánchez-Villagra MR, Salzburger W, Matschiner M. Bayesian divergence-time estimation with genome-wide single-nucleotide polymorphism data of sea catfishes (Ariidae) supports Miocene closure of the Panamanian Isthmus. *Systematic Biology* 67:681–699 (2018), Materials and Methods (SNAPP analysis settings) and Results, experiments 4 and 5. DOI <https://doi.org/10.1093/sysbio/syy006>. PMCID PMC6005153.
- Bryant D, Bouckaert R, Felsenstein J, Rosenberg NA, RoyChoudhury A. Inferring species trees directly from biallelic genetic markers: bypassing gene trees in a full coalescent analysis. *Molecular Biology and Evolution* 29:1917–1932 (2012). DOI <https://doi.org/10.1093/molbev/mss086>.
