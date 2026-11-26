# Statistical dimension lower bounds statistical query complexity

If a decision problem (distinguish $D$ from a family $\mathcal{D}$) has $\mathrm{SDA}(\mathcal{D}, \gamma) \ge d$, then every randomized statistical algorithm that solves it with success probability $\alpha > 1/2$ for every input distribution, using queries to VSTAT$(1/(3\gamma))$, must make at least $(2\alpha - 1)d$ queries. In particular an algorithm that is always correct ($\alpha = 1$), such as a deterministic one, needs at least $d$ queries, while the bound degrades to $0$ as $\alpha$ approaches $1/2$. As the main application, for every constant $\delta > 0$, every planted bipartite clique size $k \le n^{1/2 - \delta}$ and every $r > 0$, every statistical algorithm that solves the distributional planted $k$-biclique problem with probability at least $2/3$, or distinguishes it from the uniform distribution on $\{0,1\}^n$, needs at least $n^{\Omega(\log r)}$ queries to VSTAT$(n^2/(rk^2))$. Hence no polynomial-time statistical algorithm solves it with queries to VSTAT$(o(n^2/k^2))$, and every statistical algorithm needs $n^{\Omega(\log n)}$ queries to VSTAT$(n^{2-\delta}/k^2)$; this is nearly optimal, since $n$ queries to VSTAT$(16n^2/k^2)$ recover the planted set. Most practical algorithms (moment methods, local search, convex-optimization methods, MCMC and simulated annealing) can be implemented with statistical queries.

## Proof sketch

Each query $h$ can be answered with the null value $\mathbb{E}_D[h]$ for all but a $1/d$-fraction of the alternatives: if a query distinguished a large subfamily, then by Cauchy–Schwarz its discrepancy on that subfamily would be bounded by the square root of the average correlation times the query's variance, which is below the VSTAT tolerance $1/(3\gamma)$. So each query rules out few alternatives. Under the input distribution that equals $D$ with probability $1/2$ and a uniform element of a witnessing family otherwise, an algorithm with success probability $\alpha$ must answer correctly on at least a $(2\alpha - 1)$-fraction of the family, which needs $(2\alpha - 1)d$ queries. For planted bicliques, the correlation of two planted distributions grows exponentially in the overlap $|S \cap S'|$ of their planted sets, and most pairs of planted sets intersect little, which gives the statistical dimension $n^{\Omega(\log n)}$.

## Depends on

- [VSTAT oracle and statistical dimension with average correlation](vstat-oracle-statistical-dimension.md)

## Sources

- V. Feldman, E. Grigorescu, L. Reyzin, S. Vempala, Y. Xiao, "Statistical Algorithms and a Lower Bound for Detecting Planted Cliques", Journal of the ACM 64 (2017), arXiv:1201.1214, Theorem 2.9, Definition 3.6, Theorem 3.7 and Section 5.
