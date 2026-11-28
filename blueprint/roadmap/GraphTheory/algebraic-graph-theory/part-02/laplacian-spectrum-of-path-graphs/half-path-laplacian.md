# Half Laplacian of the path graph

For a natural number $n$, the half path Laplacian $A_n$ is the real $n \times n$ matrix $\tfrac12 L(P_n) = \tfrac12 (D - M)$, where $P_n$ is the path graph on the vertices $0, 1, \dots, n-1$ in which $i$ and $j$ are adjacent exactly when $|i - j| = 1$, $D$ is its diagonal degree matrix and $M$ its adjacency matrix. So for $v \in \mathbb{R}^n$,

$$(A_n v)_j = \tfrac12 \sum_{i \sim j} (v_j - v_i).$$
