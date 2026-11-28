# Absorption-time lower bound for the Moran process on graphs

**Setting.** A population of $N$ individuals occupies the vertices of a weighted directed graph $G$; $w(u,v)$ is the probability that an offspring of the individual at $u$ is placed at $v$ ($\sum_v w(u,v) = 1$). In the Moran birth-death process, at each step one individual is chosen to reproduce with probability proportional to fitness (residents $1$, mutants $r > 1$) and its offspring replaces the occupant of a vertex chosen by $w$. A single mutant is placed either uniformly at random (uniform initialization) or at vertex $v$ with probability equal to its temperature $t(v) = \frac1N\sum_u w(u,v)$ (temperature initialization). Let $\rho(G,r)$ be the resulting fixation probability, $T(G,r)$ the expected number of steps until the population is homogeneous (absorption time), and $\tau(G,r)$ the expected number of steps conditional on mutant fixation (fixation time).

**Theorem.** For every graph $G$ on $N$ vertices and either initialization, the absorption time satisfies, as $N\to\infty$,

$$T(G,r) \;\gtrsim\; \frac{\rho(G,r)}{r}\,N\log N .$$

**Corollary.** For the complete graph (well-mixed population), $T$ and $\tau$ are both of order $N\log N$; for large $N$ the absorption time is about $\frac{r+1}{r}N\log N$ and the fixation time about $\frac{r+1}{r-1}N\log N$. Hence no amplifier ($\rho(G,r) \ge \rho(K_N,r)$), and no weak suppressor (fixation probability reduced by at most a constant factor), has asymptotically shorter absorption time than the well-mixed population. A family with asymptotically shorter absorption time must have $\rho(G,r)\to 0$.

## Depends on

- [Moran Fixation](../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)

## Proof sketch

From any configuration with $k$ mutants, gaining a mutant requires that one of the $k$ mutants be chosen to reproduce, which happens with probability at most $kr/(N - k + kr)$ per step, so the expected waiting time to go from $k$ to $k+1$ mutants is at least of order $N/(kr)$. On trajectories that fix, each level $k = 1,\dots,N-1$ must be crossed, and those trajectories carry probability $\rho(G,r)$, so the absorption time is at least of order $\rho(G,r)\sum_{k=1}^{N-1} N/(kr) \approx \rho(G,r) N\log N / r$. The bound is asymptotic: for fixed small $N$ there is a directed suppressor whose fixation time is slightly shorter than that of the complete graph of the same size. The star graph, the standard amplifier, has fixation probability tending to $1 - 1/r^2$ under uniform initialization but absorption and fixation times of order $N^2\log N$.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee and M. A. Nowak, "Population structure determines the tradeoff between fixation probability and fixation time", Communications Biology 2 (2019), Introduction, Results "Amplifiers and accelerators" and Methods "Amplifiers and accelerators" (formal statements in Supplementary Note 1, Section 3.1), <https://doi.org/10.1038/s42003-019-0373-y>, PMCID PMC6478818.
