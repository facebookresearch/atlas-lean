# Graph shattering after a randomized pre-shattering phase

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. Suppose every vertex survives a randomized process (remains undecided) with probability at most $\Delta^{-c}$ for a sufficiently large constant $c$, and survival events of vertices at distance greater than some constant $k$ are independent. Then with probability at least $1 - n^{-\Omega(1)}$, every connected component of the subgraph induced by surviving vertices has $O(\Delta^{2k} \log n)$ vertices, so the remaining problem can be solved on components of size $\mathrm{poly}(\Delta) \cdot \log n$.

## Proof sketch

A connected component of size $s$ contains a set of $\Omega(s/\Delta^{2k})$ surviving vertices that are pairwise at distance between $k+1$ and $2k+1$ and connected in the power graph $G^{2k+1}$; such sets correspond to subtrees of $G^{2k+1}$, of which there are at most $n \cdot (e\Delta^{2k+1})^{t}$ of size $t$. Each is entirely surviving with probability at most $\Delta^{-ct}$ by independence, and a union bound shows no such set of size $\Omega(\log n)$ survives.

## Sources

- L. Barenboim, M. Elkin, S. Pettie, J. Schneider, "The Locality of Distributed Symmetry Breaking", Journal of the ACM 63(3) (2016); FOCS 2012.
- M. Ghaffari, "An Improved Distributed Algorithm for Maximal Independent Set", SODA 2016, arXiv:1506.05093.
