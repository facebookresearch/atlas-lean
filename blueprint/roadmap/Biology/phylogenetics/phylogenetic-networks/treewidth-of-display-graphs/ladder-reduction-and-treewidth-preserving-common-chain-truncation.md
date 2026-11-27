# Ladder reduction preserves treewidth and common chains may be truncated to four leaves

**Definitions.** An undirected graph $G$ *contains a ladder of length $k$* if the $2 \times (k+1)$ grid graph is an induced subgraph of $G$ that is attached to the rest of $G$ only through its four corner vertices. For two unrooted binary phylogenetic trees $T_1, T_2$ on the same taxon set $X$, the *display graph* $D(T_1,T_2)$ is obtained from the disjoint union of the trees by identifying leaves with the same label. A *common chain* is a sequence of taxa $x_1,\dots,x_k$ whose pendant leaves hang in the same order along a path in both trees; the *common chain reduction* truncates such a chain to a bounded number of taxa, and the *subtree reduction* replaces a common pendant subtree by a single leaf. Both preserve the tree dissimilarities (TBR distance, hybridization-type measures) for which they were introduced.

**Theorem (ladders).**
1. If $\mathrm{tw}(G) \ge 4$ and $G$ has a ladder of length at least $3$, the ladder can be lengthened arbitrarily without changing the treewidth.
2. For every graph $G$ (any treewidth), if $G$ has a ladder of length at least $4$, the ladder can be lengthened arbitrarily without changing the treewidth. Equivalently, reducing every ladder of $G$ to length $4$ preserves $\mathrm{tw}(G)$.
3. The constant $4$ is best possible: there are graphs in which shortening a ladder to length $3$ lowers the treewidth.

**Theorem (display graphs).** Let $T_1 \neq T_2$ be unrooted binary phylogenetic trees on $X$ with $|X| \ge 4$. Exhaustive application of the subtree reduction and of the common chain reduction with chains truncated to $4$ leaves does not change $\mathrm{tw}(D(T_1,T_2))$. Truncating common chains to $3$ leaves can decrease the treewidth, so $4$ is optimal.

Consequently, minimal forbidden minors for the class of graphs of treewidth at most $k$ contain no ladders of length greater than $4$.

## Expansion

An earlier result gave a ladder-length threshold $f(k)$ depending on the treewidth $k$, derived from forbidden-minor theory; the point here is a universal constant. Given an optimal tree decomposition of the graph with a short ladder, one constructs a decomposition of the lengthened graph of the same width by locating a small separator inside the ladder (a "buffer" square at each end blocks separators that cut across the ladder in the wrong place) and repeating the bags of the middle rungs. A common chain of $k$ taxa produces a ladder with $k-1$ squares in the display graph; a taxon that sits on opposite sides of the chain in the two trees supplies the extra cycle playing the role of the buffer square, so the graph result transfers to display graphs.

## Sources

- Steven Chaplick, Steven Kelk, Ruben Meuwese, Matus Mihalak and Georgios Stamoulis, "Snakes and Ladders: A Treewidth Story", Lecture Notes in Computer Science (2023), 187–200, <https://doi.org/10.1007/978-3-031-43380-1_14>; numbering as in arXiv:2302.10662: Theorems 2–4 and Corollary 1 (Sections 3–5).
