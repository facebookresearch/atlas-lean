# Statistical dimension lower bounds statistical query complexity

If a decision problem has $\mathrm{SDA}(\mathcal{D}, \gamma) \ge d$, then every statistical algorithm that solves it (with probability greater than $1/2$ over its randomness, for every input distribution) using queries to VSTAT$(1/(3\gamma))$ must make at least $d$ queries. As the main application, for every constant $\delta > 0$ and planted bipartite clique size $k \le n^{1/2 - \delta}$, every statistical algorithm detecting a planted bipartite $k$-clique (or planted dense subgraph) needs $n^{\Omega(\log n)}$ queries to VSTAT$(t)$ for $t$ of order $n^2/k^2$ up to lower-order factors, a nearly optimal lower bound. Most practical algorithms — moment methods, local search, convex-optimization methods, MCMC and simulated annealing — can be implemented with statistical queries.

## Proof sketch

Each query $h$ can be answered with the null value $\mathbb{E}_D[h]$ for all but a $1/d$-fraction of the alternatives: if a query distinguished a large subfamily, then by Cauchy–Schwarz its discrepancy on that subfamily would be bounded by the square root of the average correlation times the query's variance, which is below the VSTAT tolerance $1/(3\gamma)$. So each query rules out few alternatives and $d$ queries are needed. For planted bicliques, the correlation of two planted distributions grows exponentially in the overlap $|S \cap S'|$ of their planted sets, and most pairs of planted sets intersect little, which gives the statistical dimension $n^{\Omega(\log n)}$.

## Depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Sources

- V. Feldman, E. Grigorescu, L. Reyzin, S. Vempala, Y. Xiao, "Statistical Algorithms and a Lower Bound for Detecting Planted Cliques", Journal of the ACM 64 (2017), arXiv:1201.1214.
