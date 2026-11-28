# Absorption-time lower bound for the Moran process on graphs

**Setting.** A population of $N$ individuals occupies the vertices of a weighted directed graph $G$; $w(u,v)$ is the probability that an offspring of the individual at $u$ is placed at $v$ ($\sum_v w(u,v) = 1$). In the Moran birth-death process, at each step one individual is chosen to reproduce with probability proportional to fitness (residents $1$, mutants $r > 1$) and its offspring replaces the occupant of a vertex chosen by $w$. A single mutant is placed either uniformly at random (uniform initialization) or at vertex $v$ with probability equal to its temperature $t(v) = \frac1N\sum_u w(u,v)$ (temperature initialization). Let $\rho(G,r)$ be the resulting fixation probability, $T(G,r)$ the expected number of steps until the population is homogeneous (absorption time), and $\tau(G,r)$ the expected number of steps conditional on mutant fixation (fixation time).

**Theorem.** For every graph $G$ on $N \ge 2$ vertices (directed edges, edge weights and self-loops allowed), every $r > 1$ and either initialization, the absorption time satisfies

$$T(G,r) \;\ge\; \frac{\rho(G,r)}{r}\,N\,H_{N-1}, \qquad H_{N-1} = \sum_{k=1}^{N-1}\frac1k \;\ge\; \log N .$$

In particular $T(G,r) \ge \frac{\rho(G,r)}{r}N\log N$ for every $N \ge 2$, and $T(A,r) \ge \frac{r-1}{r^2}N\log N$ for every amplifier $A$, since then $\rho(A,r) \ge \rho(K_N,r) = \frac{1-1/r}{1-1/r^N} \ge 1 - \frac1r$. The same bound holds for any initialization scheme, with $\rho$ the fixation probability under that scheme (for example a mutant placed at a fixed vertex).

**Corollary.** For the complete graph (well-mixed population), $T$ and $\tau$ are both of order $N\log N$; for large $N$ the absorption time is about $\frac{r+1}{r}N\log N$ and the fixation time about $\frac{r+1}{r-1}N\log N$. Hence no amplifier ($\rho(G,r) \ge \rho(K_N,r)$), and no weak suppressor (fixation probability reduced by at most a constant factor), has asymptotically shorter absorption time than the well-mixed population. A family with asymptotically shorter absorption time must have $\rho(G,r)\to 0$.

## Depends on

- [Moran Fixation](../../../isothermal-theorem-for-evolutionary-graph-dynami/moran-fixation.md)
- [Amplifiers, strong amplifiers and initialization schemes](../amplifiers-of-natural-selection/amplifiers-strong-amplifiers-and-initialization-schemes.md)

## Proof sketch

Restart the process with a fresh single mutant (placed by the same initialization) whenever the mutants go extinct. The restarted process always fixes, and its expected duration is $T(G,r)/\rho(G,r)$, since the number of attempts is geometric with success probability $\rho$ and each attempt lasts $T$ steps on average. From a configuration with mutant set $X$, gaining a mutant requires that a mutant be chosen to reproduce, which has probability $r|X|/(N + (r-1)|X|) \le r|X|/N$. Every trajectory of the restarted process must, for each $k = 1, \dots, N-1$, reach $k$ mutants and gain one from there, so it spends at least $N/(rk)$ steps in expectation at level $k$. Summing over $k$ gives $T/\rho \ge \frac{N}{r}H_{N-1}$. The bound concerns the unconditional absorption time; the fixation time $\tau$ can be shorter than $T$ on directed graphs, and on the directed graph with vertices $u, v_1, v_2$ and edges $u \to v_1$, $u \to v_2$, $v_1 \leftrightarrow v_2$ at $r = 4$ under uniform initialization, one has $\tau = 3.25 < \tau(K_3, 4) = 3 + 4/7$ while $T = 79/4 = 19.75$ (Supplementary Note 1, remark after Theorem 1, prints $19.25$, a slip: averaging $13/4$ from $u$ and $28$ from each of $v_1, v_2$ gives $79/4$). The star graph, the standard amplifier, has fixation probability tending to $1 - 1/r^2$ under uniform initialization but absorption and fixation times of order $N^2\log N$.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee and M. A. Nowak, "Population structure determines the tradeoff between fixation probability and fixation time", Communications Biology 2 (2019), Introduction, Results "Amplifiers and accelerators" and Methods "Amplifiers and accelerators" (formal statements in Supplementary Note 1, Theorem 1 of Section 3.1 and the remarks after it), <https://doi.org/10.1038/s42003-019-0373-y>, PMCID PMC6478818.
