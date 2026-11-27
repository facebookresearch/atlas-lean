# Site fixation probabilities and the neutral substitution rate

**Setting.** A haploid asexual population occupies $N$ sites, each always holding one individual. At each time step a replacement event occurs: a random set of sites is refilled by offspring of other sites, drawn from a fixed distribution (the replacement rule) that does not depend on the alleles present, since all variants are neutral. Let $e_{ij} \ge 0$ be the marginal probability that, in one step, the occupant of site $j$ is replaced by an offspring of site $i$. Define the birth and death (turnover) rates

$$b_i = \sum_{j=1}^{N} e_{ij}, \qquad d_i = \sum_{j=1}^{N} e_{ji}, \qquad B = \sum_i b_i = \sum_i d_i ,$$

and measure time in generations of $N/B$ steps. Assume the replacement graph allows fixation (some site can reach every other site through chains of positive $e_{ij}$).

**Site fixation probabilities.** Let $\rho_i$ be the probability that a new neutral mutation arising at site $i$ eventually fixes. Then $(\rho_1,\dots,\rho_N)$ is the unique solution of

$$d_i \rho_i = \sum_{j=1}^{N} e_{ij}\rho_j \quad (i = 1,\dots,N), \qquad \sum_{i=1}^{N}\rho_i = 1 .$$

The quantity $\rho_i$ is the reproductive value of site $i$.

**Substitution rate.** If each birth carries a new mutation with probability $u \ll 1$, mutations arise at site $i$ in proportion to its turnover $d_i$, so the overall fixation probability of a new mutation and the substitution rate per generation are

$$\rho = \frac{1}{B}\sum_{i=1}^{N} d_i\rho_i, \qquad K = N u \rho = \frac{N u}{B}\sum_{i=1}^{N} d_i \rho_i .$$

Equivalently, since $\bar\rho = 1/N$ and $\bar d = B/N$ (bars denote averages over sites),

$$K > u \iff \overline{d\rho} > \bar d\,\bar\rho ,$$

so the clock is accelerated exactly when turnover and reproductive value are positively correlated across sites, and slowed exactly when they are negatively correlated.

## Depends on

- [Long-run expected calendar-time rate of neutral substitution](../../../long-run-neutral-substitution-rate-law-of-large.md)

## Expansion

The probability that the current occupant of site $i$ is the eventual common ancestor of the whole population is $\rho_i$, and exactly one site holds that ancestor, giving $\sum_i \rho_i = 1$. Conditioning on the next replacement event affecting site $i$, the ancestral probability of site $i$ is lost at rate $d_i$ and gained from offspring placed at site $j$ at rate $e_{ij}$, which is the balance equation $d_i\rho_i = \sum_j e_{ij}\rho_j$; this says that $\rho$ is a left null vector of the generator built from $e$, unique under the reachability assumption. A fraction $d_i/B$ of all births, hence of all new mutations, occurs at site $i$, which gives $\rho$ and $K$. In a well-mixed population ($e_{ij}$ constant) or whenever all sites are equivalent under a symmetry, $\rho_i = 1/N$ and Kimura's identity $K = u$ is recovered. In units of time steps the rate is $\tilde K = u\sum_i d_i\rho_i$.

## Sources

- B. Allen, C. Sample, Y. Dementieva, R. C. Medeiros, C. Paoletti and M. A. Nowak, "The molecular clock of neutral evolution can be accelerated or slowed by asymmetric spatial structure", PLoS Computational Biology 11 (2015), e1004108, Results, "Obtaining the neutral substitution rate", Eqs. (1)–(4), and "Effects of spatial structure", <https://doi.org/10.1371/journal.pcbi.1004108>, PMCID PMC4342344.
