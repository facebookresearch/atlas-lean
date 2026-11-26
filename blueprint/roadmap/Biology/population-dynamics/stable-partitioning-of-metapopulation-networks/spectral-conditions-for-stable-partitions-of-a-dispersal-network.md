# Spectral conditions for stable partitions of a dispersal network

**Setting.** $n$ species live on $m$ habitat patches with local dynamics $\dot x_{i,j} = f_{i,j}(x_{1,j},\dots,x_{n,j})$ and disperse symmetrically along the links of a patch graph with per-capita rates $d^i_{jk} = d^i_{kj}$ and dispersal loss $l_i$:

$$\dot x = f(x) - Lx - Ex, \qquad L = \mathcal{L}_1 \oplus \dots \oplus \mathcal{L}_n, \qquad E = l_1 I_m \oplus \dots \oplus l_n I_m,$$

where $\mathcal{L}_i$ is the weighted Laplacian of the dispersal graph of species $i$. Perturbations of a positive equilibrium $\bar x$ evolve by $\dot\varepsilon = (Df(\bar x) - L - E)\varepsilon$, so a larger algebraic connectivity (Fiedler value) $\lambda_2(\mathcal{L})$ damps spatially non-uniform perturbations. Call a simple connected weighted graph $G$ **stable** if $\lambda_2(G) \ge \tau$ for a preset threshold $\tau > 0$, and a partition of $G$ stable if each component is stable. For a cut separating $G$ into components $G_i$, the **internal cost** $I_i(s)$ of a node $s \in G_i$ is the total weight of its edges inside $G_i$ and its **external cost** $E_i(s)$ the total weight of its edges leaving $G_i$.

**Theorem.** Let $G$ be stable with $n \ge 4$ nodes, partitioned into components $G_1,\dots,G_k$ of sizes $n_i \ge 2$.

1. (Necessary condition) If every $G_i$ is stable, then $I^1_i + I^2_i \ge \tau$ for all $i$, where $I^1_i \le I^2_i$ are the two smallest internal costs in $G_i$.
2. (Sufficient condition) If the largest external cost $E^*_i$ of $G_i$ satisfies $E^*_i \le \lambda_2(G) - \tau$, then $G_i$ is stable.
3. (Fiedler-vector cut) If $n \ge 3$, $Y$ is a Fiedler vector of $\mathcal{L}(G)$ and $W = \{v : Y(v) = 0\} \ne \emptyset$, then every component of $G - W$ is stable whenever its largest external cost is at most $\lambda_2(G) - \tau$.
4. (Two-way cut) For a bipartition $G = G_1 \cup G_2$ and Fiedler vector $Y$, $G$ is stable if and only if, for $G_i$, either $\sum_{s \in G_i}Y(s) > 0$ and $\sum_{s \in G_i}(E(s) - \tau)Y(s) \ge \sum_{s \notin G_i}E(s)Y(s)$; or $\sum_{s \in G_i}Y(s) < 0$ with the reverse inequality; or $\sum_{s \in G_i}Y(s) = 0$ and $\sum_{s \in G_i}E(s)Y(s) = \sum_{s \notin G_i}E(s)Y(s)$.

## Expansion

For (1), Schur's majorization inequality for the symmetric matrix $\mathcal{L}(G_i)$ gives $\lambda_1 + \lambda_2 \le d_{n-1} + d_n$, the sum of its two smallest diagonal entries; since $\lambda_1 = 0$ and the diagonal entries are the internal costs, $\lambda_2(G_i) \le I^1_i + I^2_i$. For (2), the principal submatrix of $\mathcal{L}(G)$ on $G_i$ is $\mathcal{L}(G_i) + D_i$ with $D_i$ the diagonal of external costs; Cauchy interlacing gives $\lambda_2(G) \le \lambda_2(\mathcal{L}(G_i) + D_i)$ and Weyl's inequality bounds the right side by $\lambda_2(G_i) + E^*_i$. In (3) the Fiedler vector restricted to each component of $G - W$ is an eigenvector of the corresponding principal submatrix with eigenvalue $\lambda_2(G)$, which interlacing forces to be its first or second eigenvalue, and the Weyl step repeats. (4) follows from writing the eigen-equation in block form for the bipartition and summing.

## Sources

- Dinesh Kumar, Soumyendu Raha, "Stabilized Partitioning of Metapopulations Networks", arXiv (2019). Section 2 (metapopulation model and linearization), Section 3 (Theorems 3.1–3.4). <https://doi.org/10.48550/arXiv.1904.09800>
