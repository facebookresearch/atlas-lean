# Characterizations of forest-based networks

A **network** on a finite set $X$ is a connected, acyclic, semi-binary directed graph with leaf set $X$ and at least one root, every root having out-degree at least $2$; it is an **$m$-network** if it has $m$ roots and a phylogenetic network if $m = 1$. Hybrid vertices are internal vertices of in-degree at least $2$. A network $N = (V, A)$ is **forest-based** if there is $A' \subseteq A$ such that $F' = (V, A')$ is a forest with the same leaf set as $N$ and every arc of $A \setminus A'$ (a **contact arc**) joins vertices in different trees of $F'$. Suppressing degree-two vertices of $F'$ gives a **base forest** $F$; $N$ is **proper** forest-based if some base forest has exactly $m$ components. $N$ is **arboreal** if its underlying undirected graph is a tree, in which case $|H(N)| = |R(N)| - 1$.

**Lemma.** $N$ is forest-based if and only if there is $I \subseteq A$ such that $(V, A \setminus I)$ is a forest, every arc of $I$ joins different trees of this forest, and every non-leaf vertex is the tail of some arc not in $I$.

**Theorem 1 (trivial forest).** The following are equivalent: (i) $N$ is forest-based; (ii) $N$ is based on the trivial forest, whose components are the single elements of $X$; (iii) the trivial forest embeds in $N$ as a union of vertex-disjoint paths, one ending at each leaf, with no arc of $N$ joining two non-consecutive vertices of the same path. Consequently a forest-based $m$-network has $|X| \ge m$, it has a non-proper base forest if $|X| > m$, and it is proper if $|X| = m$.

**Relations to other classes (binary phylogenetic networks).**
- Every forest-based phylogenetic network is tree-based.
- Every tree-child network, and in particular every phylogenetic tree, is forest-based: removing all arcs into hybrid vertices leaves a valid subdivision forest.

**Theorem 3 (arboreal networks).** An arboreal network with at least two leaves is forest-based if and only if for every hybrid vertex $h$ there are distinct vertices $h = v_1, \dots, v_k$ ($k \ge 1$) such that consecutive vertices share a hybrid child and $v_k$ has a non-hybrid child. In that case $N$ is proper forest-based.

**Theorem 6 (cluster invariance).** If $N_1, N_2$ are distinct arboreal networks on $X$ with the same cluster system, then $N_1$ is forest-based if and only if $N_2$ is.

## Expansion

Starting from any base forest, splitting each component into root-to-leaf paths (keeping one outgoing arc per branching vertex and declaring the others contact arcs) gives a base forest of single leaves, which is Theorem 1. The extra condition on paths prevents a contact arc from joining two vertices of the same tree. For binary networks, attaching each non-root tree of a base forest to the network by one incoming arc of its root produces a base tree, so forest-based implies tree-based. The converse fails, so the forest-based class lies strictly between tree-child and tree-based networks. In an arboreal network a contact arc can be removed at a hybrid vertex only if some vertex still has a non-hybrid child to keep it internal, which gives the chain condition of Theorem 3. Arboreal networks with equal cluster systems differ only by collapsing "bad" arcs between hybrid vertices, an operation that preserves the chain condition. Proper forest-based networks are characterized by colourings of an associated graph, a 2-colouring when $m = 2$, and no efficient recognition algorithm is known in general.

## Sources

- K. T. Huber, V. Moulton, G. E. Scholz, "Forest-based networks", Bulletin of Mathematical Biology (2022), Sections 2–5, Lemma 1, Theorem 1, Proposition 1, Theorems 2–3 and Theorem 6, <https://doi.org/10.1007/s11538-022-01081-9>, PMCID PMC9477957.
