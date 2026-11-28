# Max-entropy spanning tree distributions are lambda-uniform and approximately computable

Let $G=(V,E)$ be connected with $n \ge 2$ vertices, the domain of the spanning tree polytope $P_{\mathrm{ST}}(G)$. (For $n=1$ the only spanning tree is empty, so every $z \in P_{\mathrm{ST}}(G)$ has empty positive support and the minimum $\min_{e \in E_+} z_e$ in (iii) does not exist.)

(i) For every $z$ in the relative interior of $P_{\mathrm{ST}}(G)$ the maximum-entropy distribution with marginals $z$ is unique and equals $\mu_\lambda$ for some $\lambda \in \mathbb{R}_{> 0}^{E}$.

(ii) For every $\lambda > 0$ and $e=uv \in E$, $\mathbb{P}_{T \sim \mu_\lambda}[e \in T]=\lambda_e\,R^{\lambda}_{\mathrm{eff}}(u,v)$, where $R^{\lambda}_{\mathrm{eff}}$ is the effective resistance in the electrical network with conductances $\lambda$.

(iii) Let $z \in P_{\mathrm{ST}}(G)$ and let $E_+=\{e \in E : z_e > 0\}$ be its positive support; the graph $(V,E_+)$ is connected, since $z(\delta(S)) \ge (n-1)-(|S|-1)-(n-|S|-1)=1$ for every proper nonempty $S$. For every $\varepsilon > 0$ one can compute $\lambda \in \mathbb{R}_{>0}^{E_+}$, extended by $\lambda_e=0$ for $e \notin E_+$, such that the $\lambda$-uniform distribution $\mu_\lambda$ on the spanning trees of $(V,E_+)$ satisfies $\mathbb{P}_{\mu_\lambda}[e \in T] \le (1+\varepsilon)z_e$ for all $e \in E$, in time polynomial in $n$, $-\log\min_{e \in E_+} z_e$ and $\log(1/\varepsilon)$. Edges outside $E_+$ then have marginal $0$. Restricting to $E_+$ is necessary: if $G$ is a triangle and $z$ is the incidence vector of one of its spanning trees, the omitted edge has $z_e=0$ but positive marginal under every strictly positive $\lambda$, and $\log\min_{e \in E} z_e$ is undefined.

## Proof sketch

Slater's condition holds in the relative interior, so strong duality applies to the entropy program; stationarity of the Lagrangian forces $\mu(T) \propto \exp(\sum_{e \in T}\gamma_e)$, i.e. $\lambda_e=e^{\gamma_e}$, and strict concavity of entropy gives uniqueness. The marginal formula follows by differentiating the matrix-tree determinant in $\lambda_e$, which yields Kirchhoff's resistance formula. For (iii), applied to $(V,E_+)$ and the restriction of $z$, the dual objective $\log\sum_{T}e^{\gamma(T)}-\gamma^{\top}z$ is convex with gradients computable by determinants, so the ellipsoid method or interior point methods find a near-optimal $\gamma$.

## Depends on

- [Maximum-entropy and lambda-uniform distributions over spanning trees](max-entropy-spanning-tree-distribution.md)
- [Spanning tree polytope of a connected graph](spanning-tree-polytope.md)
- [Effective resistance](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/effective-resistance.md)

## Proof depends on

- [Kirchhoff's matrix-tree theorem](../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md)
- [Kirchhoff's effective resistance formula, weighted](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/kirchhoff-effective-resistance-formula-weighted.md)
- [Strong duality under Slater's condition](../../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-eq-primal-value-of-slater.md)
- [The ellipsoid method finds a point](../../../../Analysis/convex-analysis-and-variations/ellipsoid-method/ellipsoid-run-finds-point.md)

## Sources

- Arash Asadpour, Michel X. Goemans, Aleksander Madry, Shayan Oveis Gharan, Amin Saberi, "An O(log n/log log n)-Approximation Algorithm for the Asymmetric Traveling Salesman Problem", Operations Research (2017), Theorem 5.2.
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Theorem 1.3.
- Mohit Singh, Nisheeth K. Vishnoi, "Entropy, Optimization and Counting", STOC (2014), arXiv:1304.8108.
