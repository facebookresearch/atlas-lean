# Max-entropy spanning tree distributions are lambda-uniform and approximately computable

Let $G=(V,E)$ be connected with $n$ vertices.

(i) For every $z$ in the relative interior of $P_{\mathrm{ST}}(G)$ the maximum-entropy distribution with marginals $z$ is unique and equals $\mu_\lambda$ for some $\lambda \in \mathbb{R}_{> 0}^{E}$.

(ii) For every $\lambda > 0$ and $e=uv \in E$, $\mathbb{P}_{T \sim \mu_\lambda}[e \in T]=\lambda_e\,R^{\lambda}_{\mathrm{eff}}(u,v)$, where $R^{\lambda}_{\mathrm{eff}}$ is the effective resistance in the electrical network with conductances $\lambda$.

(iii) For every $z \in P_{\mathrm{ST}}(G)$ and $\varepsilon > 0$ one can compute $\lambda$ with $\mathbb{P}_{\mu_\lambda}[e \in T] \le (1+\varepsilon)z_e$ for all $e \in E$ in time polynomial in $n$, $-\log\min_e z_e$ and $\log(1/\varepsilon)$.

## Proof sketch

Slater's condition holds in the relative interior, so strong duality applies to the entropy program; stationarity of the Lagrangian forces $\mu(T) \propto \exp(\sum_{e \in T}\gamma_e)$, i.e. $\lambda_e=e^{\gamma_e}$, and strict concavity of entropy gives uniqueness. The marginal formula follows by differentiating the matrix-tree determinant in $\lambda_e$, which yields Kirchhoff's resistance formula. For (iii) the dual objective $\log\sum_{T}e^{\gamma(T)}-\gamma^{\top}z$ is convex with gradients computable by determinants, so the ellipsoid method or interior point methods find a near-optimal $\gamma$.

## Depends on

- [Maximum-entropy and lambda-uniform distributions over spanning trees](max-entropy-spanning-tree-distribution.md)
- [Kirchhoff's matrix-tree theorem](../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md)
- [Kirchhoff's effective resistance formula, weighted](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/kirchhoff-effective-resistance-formula-weighted.md)
- [Strong duality under Slater's condition](../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-eq-primal-value-of-slater.md)
- [The ellipsoid method finds a point](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/ellipsoid-run-finds-point.md)

## Proof depends on

- [Maximum-entropy and lambda-uniform distributions over spanning trees](max-entropy-spanning-tree-distribution.md)
- [Kirchhoff's matrix-tree theorem](../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md)
- [Kirchhoff's effective resistance formula, weighted](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/kirchhoff-effective-resistance-formula-weighted.md)
- [Strong duality under Slater's condition](../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-eq-primal-value-of-slater.md)
- [The ellipsoid method finds a point](../../../Analysis/convex-analysis-and-variations/ellipsoid-method/ellipsoid-run-finds-point.md)

## Sources

- Arash Asadpour, Michel X. Goemans, Aleksander Madry, Shayan Oveis Gharan, Amin Saberi, "An O(log n/log log n)-Approximation Algorithm for the Asymmetric Traveling Salesman Problem", Operations Research (2017).
- Mohit Singh, Nisheeth K. Vishnoi, "Entropy, Optimization and Counting", STOC (2014), arXiv:1304.8108.
