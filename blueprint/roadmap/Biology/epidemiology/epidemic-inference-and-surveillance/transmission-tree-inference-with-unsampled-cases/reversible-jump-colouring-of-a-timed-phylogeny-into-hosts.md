# Reversible-jump colouring of a timed phylogeny into hosts

Let $\mathcal P$ be a timed phylogeny of pathogen genomes, one per sampled case, $T$ a transmission
tree, $\theta$ the transmission and sampling parameters and $N_e g$ the within-host effective
population size times generation time. Assume a complete transmission bottleneck (a single
lineage is transmitted) and that one genome is sequenced per sampled host. Then $\mathcal P$ splits
into within-host subtrees, one per included host, and

$$P(\theta, N_e g, T \mid \mathcal P) \propto P(\mathcal P \mid N_e g, T)\, P(T \mid \theta)\,
P(\theta)\, P(N_e g),$$

where $P(\mathcal P \mid N_e g, T)$ is the product of the within-host coalescent likelihoods of the
subtrees and $P(T \mid \theta)$ is the transmission-tree probability for a finished or ongoing
outbreak. Transmission events are points placed on the branches of $\mathcal P$, so the number of
hosts is variable. If $T$ has $n$ hosts of which $\sum_i s_i$ are sampled, a move that adds a
transmission event uniformly on the branches of $\mathcal P$ (total length $|\mathcal P|$) to give
$T'$ is accepted with probability

$$\min\!\left(1,\ \frac{P(T' \mid \theta)}{P(T \mid \theta)}\,
\frac{P(\mathcal P \mid T', N_e g)}{P(\mathcal P \mid T, N_e g)}\,
\frac{|\mathcal P|}{n + 1 - \sum_{i=1}^{n} s_i}\right),$$

and the reverse move, which removes one of the $n - \sum_i s_i$ removable events chosen uniformly,
with probability

$$\min\!\left(1,\ \frac{P(T' \mid \theta)}{P(T \mid \theta)}\,
\frac{P(\mathcal P \mid T', N_e g)}{P(\mathcal P \mid T, N_e g)}\,
\frac{n - \sum_{i=1}^{n} s_i}{|\mathcal P|}\right).$$

## Depends on

- [Likelihood of a partially sampled transmission tree](likelihood-of-a-partially-sampled-transmission-tree.md)
- [Transmission-tree likelihood for an ongoing outbreak](transmission-tree-likelihood-for-an-ongoing-outbreak.md)

## Expansion

With a complete bottleneck, lineages in different hosts evolve independently, so the phylogeny
likelihood factorizes over hosts, each factor being a coalescent with constant size $N_e g$. Each
unsampled host corresponds to one removable transmission event, so after an addition there are
$n + 1 - \sum_i s_i$ removable events; the ratio of proposal densities (uniform position on a tree
of length $|\mathcal P|$ versus a uniform choice among removable events) gives the
Metropolis–Hastings–Green factors, and the two moves are mutual inverses. Standard
Metropolis–Hastings updates of $r$, $p$, $\pi$ and $N_e g$ complete the sampler.

## Sources

- X. Didelot, C. Fraser, J. Gardy, C. Colijn, "Genomic infectious disease epidemiology in
  partially sampled and ongoing outbreaks", Molecular Biology and Evolution 34 (2017) 997-1007,
  "Overview of Inference Strategy" (Eq. 1) and "Inference of Transmission Tree Given a Phylogeny"
  (Eqs. 12-13), <https://doi.org/10.1093/molbev/msw275> (PMC5850352).
