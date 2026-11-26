# Robust orientability of unrooted phylogenetic networks

**Setting.** An unrooted phylogenetic network $N$ is a connected undirected graph whose degree-1 vertices are the labeled leaves. Rooting $N$ on an edge $e$ means subdividing $e$ by a root vertex $\rho$ and orienting every edge. An orientation is *phylogenetic* if the result is a rooted phylogenetic network: a single root, acyclic, at least one leaf, and the leaves are the only vertices of out-degree $0$. $N$ is *robustly orientable* if for every edge $e$ there is a phylogenetic orientation rooted on $e$. A *blob* is a nontrivial biconnected component; a *sink component* is a biconnected component incident with exactly one cut-edge. $N$ is *level-$k$* if every blob of $N$ becomes a tree after deleting at most $k$ edges.

**Theorem 2.16.** In every phylogenetic orientation with root $\rho$, every cut-edge of $N$ is oriented away from $\rho$.

**Theorem 3.1.** An unrooted phylogenetic network is robustly orientable if and only if it contains no sink component.

**Theorem 3.3.** Every tree-based unrooted phylogenetic network (one with a spanning tree whose leaves are exactly the leaves of $N$) is robustly orientable.

**Theorem 3.5.** For $k\le2$, every level-$k$ unrooted binary phylogenetic network is robustly orientable.

## Expansion

If a sink component $B$ hangs from the rest of $N$ by a single cut-edge and the root is placed outside $B$, that cut-edge points into $B$ (Theorem 2.16), so every vertex of $B$ is reachable only through it; an acyclic orientation of the finite blob then has a vertex of out-degree $0$ inside $B$ that is not a leaf, which is forbidden. Conversely, without sink components every blob has at least two incident cut-edges, so it has an exit. Orient the blob containing the root, or the blob reached first, by an $st$-numbering: for a biconnected graph $G$ and any edge $\{s,t\}$, $G\setminus\{s,t\}$ has an acyclic orientation with $s$ the only source and $t$ the only sink (Theorem 2.20), taking $s$ at the entry and $t$ at an exit cut-edge; proceeding outward along cut-edges orients the whole network. Tree-based and low-level networks have no sink components because every blob carries leaves or at least two cut-edges.

## Sources

- T. Britz, M. Hendriksen, K. O'Reilly, "Classes of phylogenetic networks that are robust to root placement", arXiv preprint (2026), Theorems 2.16, 2.20, 3.1, 3.3 and 3.5, <https://doi.org/10.48550/arXiv.2607.15625>.
