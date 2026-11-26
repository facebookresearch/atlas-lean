# Coalescence probability under a discrete-time migration matrix

Let two subpopulations have sizes $N_1(g)$ and $N_2(g)$ at generation $g$ in the past and exchange migrants with the backwards-in-time one-generation matrix

$$M(g) = \begin{pmatrix} 1 - m_{12}(g) & m_{12}(g) \\ m_{21}(g) & 1 - m_{21}(g) \end{pmatrix},$$

where $m_{12}(g)$ is the probability that a lineage currently in population $1$ had its parent in population $2$. For a lineage sampled in population $k$, let $a_i(g)$ be the row vector of probabilities that its ancestor at generation $g$ lies in each population; then $a_i(g) = a_i(0)\prod_{h=1}^{g} M(h)$. Writing $\Lambda(g)$ for the diagonal matrix with entries $1/N_1(g)$ and $1/N_2(g)$, the probability that two lineages coalesce between generations $g-1$ and $g$, given that they have not coalesced earlier, is

$$c(g) \;=\; a_i(g)\, \Lambda(g)\, a_j(g)^{\mathsf T},$$

that is, the chance that both ancestors are in the same subpopulation weighted by the reciprocal of that subpopulation's size, and the unconditional coalescence density at generation $g$ is

$$\pi(g) \;=\; c(g) \prod_{h=1}^{g-1} \bigl( 1 - c(h) \bigr).$$

Substituting $\pi$ into the discrete form of the expected-sharing integral gives the expected fraction of genome shared through segments in a length range under an arbitrary history of sizes and migration rates.

## Depends on

- [Expected IBD sharing from coalescence times and Erlang segment lengths](expected-ibd-sharing-from-coalescence-times-and-erlang-segment-lengths.md)
- [Probability of no coalescence in one Wright–Fisher generation](../../kingman-s-coalescent-and-watterson-s-estimator/no-coal-prob.md)
- [Finite-state Markov chain with a given transition matrix](../../../../Probability/markov-chains/finite-markov-chains/is-finite-markov-chain.md)

## Expansion

The formulation is general enough to encode population splits and admixture pulses: setting $m_{12}(g) = m_{21}(g) = 0$ for $g < G$ and merging the two populations at $g = G$ encodes a split $G$ generations ago, and a single generation with large $m$ encodes an admixture pulse. If the ancestral population is assumed to have constant size from some generation $G$ into the indefinite past, the tail of the product has a closed form and only the first $G$ terms need to be accumulated, whatever the size trajectory before $G$. Because haplotype sharing is informative mainly about the recent past, where coalescence probabilities per generation are small, the product is close to one over the informative range, and the method resolves splits and migration on the order of tens to hundreds of generations — a regime in which methods based on local-ancestry deconvolution lose power because the exchanging populations are too similar to be told apart marker by marker.

## Sources

- P. F. Palamara, I. Pe'er, "Inference of historical migration rates via haplotype sharing", *Bioinformatics* 29 (2013), i180–i188, <https://doi.org/10.1093/bioinformatics/btt239> (PMC3694674). Methods, "IBD distributions in the presence of migration" and "The general case", Equations (4)–(14).
