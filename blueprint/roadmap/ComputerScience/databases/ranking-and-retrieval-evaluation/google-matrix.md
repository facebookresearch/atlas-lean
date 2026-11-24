# Google matrix

Fix $n \ge 1$ nodes, a link matrix $L \in \mathbb{R}^{n \times n}$ with nonnegative entries whose every nonzero column sums to $1$ (column $j$ is zero
exactly when node $j$ is dangling, that is, has no out-links), a teleport probability vector $v$ and a damping factor $0 < \alpha < 1$. Let $P$ be
$L$ with every zero column replaced by $v$. The Google matrix is

$$G = \alpha P + (1 - \alpha)\, v \mathbf{1}^{\mathsf T}.$$

$P$ and $G$ are column-stochastic: each column of $P$ is a probability vector, and each column of $G$ is the convex combination $\alpha P_{\cdot j} + (1-\alpha) v$
of two probability vectors. Uniform teleportation, $v = \mathbf{1}/n$, is a special case. The variant that leaves dangling columns zero, so that probability
mass leaks, is outside this definition. Replacing dangling columns by $v$ itself is the strongly preferential choice; replacing them by the uniform vector
$\mathbf{1}/n$ while teleporting to $v$ (weakly preferential) gives a different matrix, and some sources also write the row-stochastic transpose.

## Sources

- D. F. Gleich, *PageRank beyond the Web*, SIAM Review 57(3) (2015), 321–363; arXiv:1407.5107, Definition 2.1 and equation (2.1) (p. 2; column-stochastic $P$, teleportation vector $v$, $0 < \alpha < 1$, and the matrix $\alpha P + (1-\alpha) v e^{\mathsf T}$), Theorem 2.5 (p. 4; $P = \bar P + v c^{\mathsf T}$ with the correction vector $c^{\mathsf T} = e^{\mathsf T} - e^{\mathsf T} \bar P$, the dangling indicator in the standard construction), and Section 3.1 (pp. 6–7; the strongly preferential construction, printed there with the outer product transposed). <https://arxiv.org/abs/1407.5107>
- A. N. Langville and C. D. Meyer, *Deeper inside PageRank*, Internet Mathematics 1(3) (2004), 335–380, Section 3 (uniform dangling, row-stochastic convention; it coincides with this definition when $v = \mathbf{1}/n$, and for general teleport $v$ it is the weakly preferential matrix).
- J. Leskovec, A. Rajaraman and J. D. Ullman, *Mining of Massive Datasets*, Chapter 5, Sections 5.1.4–5.1.5 (the uniform-teleport special case). <https://web-wp.archive.org/web/20250909051552/http://infolab.stanford.edu/~ullman/mmds/book.pdf>
