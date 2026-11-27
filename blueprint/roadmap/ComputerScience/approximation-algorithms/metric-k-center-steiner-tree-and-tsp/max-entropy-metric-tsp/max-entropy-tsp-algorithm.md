# Max-entropy rounding algorithm for metric TSP

Given a metric TSP instance $(V,c)$, the max-entropy rounding algorithm proceeds as follows.

1. Compute an optimal extreme point solution $x^0$ of the subtour elimination LP (so $\min_e x^0_e \ge 1/n!$ on its support); split an arbitrary vertex $u$ into $u_0,v_0$ joined by an edge $e_0$ with $x_{e_0}=1$, $c(e_0)=0$, assigning half of each edge at $u$ to each copy.
2. Let $G=(V,E)$ be the support of $x^0$ without $e_0$ and $x=x^0|_E$, which lies in $P_{\mathrm{ST}}(G)$ (Karlin–Klein–Oveis Gharan, Fact 2.1).
3. Compute $\lambda \in \mathbb{R}_{> 0}^{E}$ with $\mathbb{P}_{\mu_\lambda}[e \in T]=x_e(1 \pm 2^{-n})$ for all $e \in E$.
4. Sample $T \sim \mu_\lambda$, compute a minimum-cost $O$-join $M$ where $O$ is the set of odd-degree vertices of $T$, and output a Hamiltonian cycle obtained by shortcutting an Euler tour of $T \uplus M$.

This is a variant of the algorithm of Oveis Gharan, Saberi and Singh for graphic TSP.

## Depends on

- [Subtour elimination LP of a metric TSP instance](subtour-elimination-lp.md)
- [Spanning tree polytope of a connected graph](spanning-tree-polytope.md)
- [Maximum-entropy and lambda-uniform distributions over spanning trees](max-entropy-spanning-tree-distribution.md)
- [T-joins and the T-join dominant polyhedron](t-join-dominant.md)

## Sources

- Shayan Oveis Gharan, Amin Saberi, Mohit Singh, "A Randomized Rounding Approach to the Traveling Salesman Problem", FOCS (2011).
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Section 1.1 (Algorithm 1) and Facts 2.1–2.2.
