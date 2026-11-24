# McVean's genealogical model for PCA

Let $\mu$ be a measure on a measurable space $\Omega$ and $\iota$, $S$ finite sets of samples and loci. A genealogical model consists of real random genotypes $Z_{is}$ on $\Omega$, square integrable with respect to $\mu$, a real number $\theta$ and real numbers $t_{ij}$ ($i, j \in \iota$) such that

$$\int d_{ij} \, d\mu = \theta\, t_{ij} \qquad \text{for all } i, j,$$

where $d$ is the [pairwise-difference matrix](pair-diff.md) of the random genotypes. The parameters are arbitrary reals satisfying this relation. When $\mu$ is a probability measure, $\theta \ge 0$ is the scaled mutation rate and the $t_{ij} \ge 0$ are finite expected pairwise coalescence times, it is the neutral infinite-sites relation, taken as an assumption; for $\theta = 0$ the times are not determined by the genotypes.
