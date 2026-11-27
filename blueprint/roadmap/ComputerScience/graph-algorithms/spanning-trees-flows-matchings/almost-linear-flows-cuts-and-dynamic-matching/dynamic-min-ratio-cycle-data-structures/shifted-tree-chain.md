# Tree chains with shifts and rebuilds over recursive sparsified core graphs

Let $d \ge 1$ and $k = m^{1/d}$. A $d$-level tree chain of $G$ is a sequence $\mathcal{G} = \{G_0 = G, G_1, \ldots, G_d\}$ where for each $i < d$ the graph $G_i$ carries a family of $k$ low-stretch forests $\{(T_j, F_j, \widetilde{\mathrm{str}}^j)\}_{j=0}^{k-1}$ that are good on average for every edge, $\frac{1}{k}\sum_{j}\widetilde{\mathrm{str}}^j_e \le O(\log^7 n)$ for all $e$, a shift index $\mathrm{shift}_i \in \{0, \ldots, k-1\}$, initially $0$, a $(\gamma_\ell, \gamma_c)$-sparsified core graph $\mathcal{S}(G_i, F_j)$ for each $j$, and

$$
G_{i+1} = \mathcal{S}(G_i, F_{\mathrm{shift}_i}),
$$

while $G_d$ carries $\widetilde{O}(|E(G_d)|)$ low-stretch trees and a shift index $\mathrm{shift}_d$, initially $0$, selecting one of them, the bottom tree. The chain determines a spanning tree $T^{\mathcal{G}}$ of $G$, the union of the preimages of the selected forests $F^{G_0}_{\mathrm{shift}_0}, \ldots, F^{G_{d-1}}_{\mathrm{shift}_{d-1}}$ and of the bottom tree; the selected forests alone can leave $T^{\mathcal{G}}$ disconnected, and the bottom tree connects them. The operation $\mathrm{Rebuild}(i)$ reinitializes $G_i, \ldots, G_d$, and $\mathrm{Shift}(i)$ replaces $\mathrm{shift}_i$ by $\mathrm{shift}_i + 1 \bmod k$ and reinitializes $G_{i+1}, \ldots, G_d$. A branching variant keeps $\widetilde{O}(1)$ forests per level, giving $\widetilde{O}(1)^d$ chains in total.

## Depends on

- [Sparsified core graphs with short low-congestion embeddings](sparsified-core-graph-embedding.md)
- [Stretch of an edge with respect to a rooted spanning forest](rooted-forest-edge-stretch.md)

## Sources

- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
