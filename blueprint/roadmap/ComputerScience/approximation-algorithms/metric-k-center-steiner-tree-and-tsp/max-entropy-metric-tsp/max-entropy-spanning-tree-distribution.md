# Maximum-entropy and lambda-uniform distributions over spanning trees

Let $G=(V,E)$ be connected and let $\mathcal{T}$ be its set of spanning trees. For $\lambda \in \mathbb{R}_{> 0}^{E}$ the $\lambda$-uniform distribution is

$$
\mu_\lambda(T)=\frac{\prod_{e \in T}\lambda_e}{\sum_{T' \in \mathcal{T}}\prod_{e \in T'}\lambda_e}, \qquad T \in \mathcal{T}.
$$

By the weighted matrix-tree theorem the denominator equals any principal $(n-1)\times(n-1)$ minor of the weighted Laplacian $L_\lambda=\sum_{e=uv}\lambda_e(\mathbf{e}_u-\mathbf{e}_v)(\mathbf{e}_u-\mathbf{e}_v)^{\top}$. For a point $z$ in the relative interior of $P_{\mathrm{ST}}(G)$, a maximum-entropy distribution with marginals $z$ is an optimal solution of

$$
\max\Big\{-\sum_{T \in \mathcal{T}}\mu(T)\log\mu(T) : \mu \ge 0,\ \sum_{T}\mu(T)=1,\ \sum_{T \ni e}\mu(T)=z_e\ \forall e \in E\Big\}.
$$

## Depends on

- [Spanning tree polytope of a connected graph](spanning-tree-polytope.md)

## Proof depends on

- [Weighted matrix-tree theorem](../../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/weighted-matrix-tree.md)

## Sources

- Arash Asadpour, Michel X. Goemans, Aleksander Madry, Shayan Oveis Gharan, Amin Saberi, "An O(log n/log log n)-Approximation Algorithm for the Asymmetric Traveling Salesman Problem", Operations Research (2017).
- Mohit Singh, Nisheeth K. Vishnoi, "Entropy, Optimization and Counting", STOC (2014), arXiv:1304.8108.
