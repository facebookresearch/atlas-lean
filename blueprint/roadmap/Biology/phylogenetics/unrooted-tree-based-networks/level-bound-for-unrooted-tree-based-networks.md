# Level bound for unrooted tree-based networks

Let $X$ be a finite set with $|X| \ge 1$. An unrooted phylogenetic network $N$ on $X$ is a connected simple graph in which every vertex has degree $1$ or $3$ and the degree-$1$ vertices (leaves) are exactly $X$. $N$ is **tree-based** if it has a spanning tree whose leaf set is exactly $X$ (a *support tree*). A *blob* is a maximal subgraph without cut-edges that is not a single vertex; $N$ is **level-$k$** if at most $k$ edges must be removed from each blob to obtain a tree; $N$ is **proper** if deleting any cut-edge splits $X$ into two non-empty parts.

1. **Blob decomposition.** For a blob $B$, let $B_N$ be $B$ together with the cut-edges of $N$ incident to $B$. Then $N$ is tree-based if and only if $B_N$ is tree-based for every blob $B$.
2. **Necessity of properness.** Every tree-based network is proper; a network on a single leaf $\{x\}$ is tree-based only if it is the single vertex $x$.
3. **Level bound.** Every proper level-$k$ network with $k \le 4$ is tree-based. The bound is sharp: for each $k \ge 5$ there are proper level-$k$ networks (indeed strictly level-$k$ ones) that are not tree-based.

## Expansion

Every cut-edge lies in every spanning tree, so a support tree restricts to a support tree of each $B_N$, and support trees of the pieces glue back together; this is item 1. A cut-edge whose removal leaves a component with no leaf would force a blob piece with a single leaf, which cannot be tree-based, giving item 2. For item 3 it therefore suffices to treat simple networks; deleting a leaf and suppressing its neighbour preserves non-tree-basedness in reverse (if $N - x$ is tree-based then so is $N$), so one reduces to simple level-$\le 4$ networks on two leaves $\{x,y\}$, where a support tree is a Hamiltonian path from $x$ to $y$. These are checked case by case from the finitely many cubic multigraphs underlying such blobs. A specific level-$5$ network on two leaves has no Hamiltonian $x$–$y$ path, and substituting it for a pendant edge in any level-$k$ network ($k \ge 5$) keeps the level while destroying tree-basedness.

## Sources

- A. Francis, K. T. Huber, V. Moulton, "Tree-based unrooted phylogenetic networks", *Bulletin of Mathematical Biology* (2018), Section 2 (Proposition 1, Observation 1, Lemmas 2–3, Theorem 1, Remark 1), <https://doi.org/10.1007/s11538-017-0381-3> (PMC5790869).
