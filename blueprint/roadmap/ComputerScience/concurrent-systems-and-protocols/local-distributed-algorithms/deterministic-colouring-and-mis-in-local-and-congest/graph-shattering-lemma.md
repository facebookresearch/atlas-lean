# Graph shattering after a randomized pre-shattering phase

Let $G = (V, E)$ be a graph with $n$ vertices and maximum degree $\Delta \ge 2$. Consider a process which generates a random subset $B \subseteq V$ such that $\Pr[v \in B] \le \Delta^{-c_1}$ for every $v \in V$, for some constant $c_1 \ge 1$, and the indicator of the event $v \in B$ depends only on the randomness of vertices within at most $c_2$ hops from $v$, for some constant $c_2 \ge 1$. Let $H = G^{[2c_2+1,\, 4c_2+2]}$ be the graph on $V$ with an edge between $u$ and $v$ if and only if their distance in $G$ is between $2c_2 + 1$ and $4c_2 + 2$. Then for every constant $c_3 < c_1 - 4c_2 - 2$, with probability at least $1 - n^{-c_3}$ both of the following hold:

- (P1) $H[B]$ has no connected component $U$ with $\lvert U \rvert \ge \log_\Delta n$;
- (P2) every connected component of $G[B]$ has $O\bigl(\log_\Delta n \cdot \Delta^{2c_2}\bigr)$ vertices.

Since $c_2$ is a constant, the remaining problem on $B$ thus splits into components of size $\mathrm{poly}(\Delta) \cdot \log n$.

## Proof sketch

For (P1), a connected component of $H[B]$ with at least $t = \log_\Delta n$ vertices contains a $t$-vertex subtree of $H$; there are at most $4^t$ tree shapes, each embedded into $H$ in fewer than $n \cdot \Delta^{(4c_2+2)t}$ ways. Vertices at distance at least $2c_2 + 1$ in $G$ have disjoint $c_2$-neighbourhoods, so their membership events depend on disjoint random bits; Fischer and Ghaffari use this to bound the probability that a given tree lies in $B$ by $\Delta^{-c_1 t}$ (immediate when the tree's vertices are pairwise at distance at least $2c_2 + 1$, the case (P2) uses), and a union bound over all trees gives failure probability at most $n^{-c_3}$. For (P2), add the vertices of a connected component $S$ of $G[B]$ to a set $U$ greedily, each time discarding the at most $\Delta^{2c_2}$ vertices within $2c_2$ hops of the added vertex and taking next a vertex adjacent to a discarded or chosen one. The chosen vertices are pairwise at distance at least $2c_2 + 1$, each new one is at distance exactly $2c_2 + 1$ from an earlier one, so $U$ is connected in $H[B]$, and $\lvert S \rvert \ge \log_\Delta n \cdot \Delta^{2c_2}$ forces $\lvert U \rvert \ge \log_\Delta n$, which (P1) excludes. (Fischer and Ghaffari's lemma has a third property, a network decomposition of each component of $G[B]$, which this page omits.)

## Sources

- M. Fischer, M. Ghaffari, "Sublogarithmic Distributed Algorithms for Lovász Local Lemma, and the Complexity Hierarchy", DISC 2017, arXiv:1705.04840, Lemma 2.3 (The Shattering Lemma) and its proof in Appendix A.2.
- L. Barenboim, M. Elkin, S. Pettie, J. Schneider, "The Locality of Distributed Symmetry Breaking", Journal of the ACM 63(3) (2016); FOCS 2012.
- M. Ghaffari, "An Improved Distributed Algorithm for Maximal Independent Set", SODA 2016, arXiv:1506.05093, Lemmas 4.1 and 4.2.
