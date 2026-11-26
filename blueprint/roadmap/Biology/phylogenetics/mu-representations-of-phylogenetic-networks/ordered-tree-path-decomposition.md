# Ordered tree-path decompositions characterize tree-child networks

Let $\mathcal N$ be a rooted phylogenetic network on leaf set $L(\mathcal N)=\{l_1,\dots,l_n\}$ (a rooted DAG whose out-degree-0 vertices are bijectively labelled by $[n]$), with no elementary paths, i.e. no arc $(u,v)$ with $\operatorname{outdeg}(u)=1$ and $\operatorname{indeg}(v)=1$. A vertex is a **tree vertex** if its in-degree is 1 and a **reticulation** if its in-degree is at least 2; $\mathcal N$ is **tree-child** if every non-leaf vertex has at least one child that is a tree vertex. Write $u \ge v$ if there is a (possibly trivial) directed path from $u$ to $v$.

A directed path $(u_1,\dots,u_k)$ is a **tree-path** if $u_2,\dots,u_k$ are tree vertices ($u_1$ may be the root, a tree vertex or a reticulation). Tree-paths are ordered by subpath inclusion.

**Structure of maximal tree-paths.** In a tree-child network:
1. a tree-path is maximal if and only if it starts at the root or at a reticulation and ends at a leaf;
2. every leaf $l$ lies on a unique maximal tree-path $T(l)$; write $r(l)$ for its first vertex;
3. the sets $T(l_1),\dots,T(l_n)$ cover $V(\mathcal N)$.

A total order $\prec$ on $[n]$ is a **tree-path order** if $r(l_i) > r(l_j)$ implies $i \prec j$. For such an order put $P_\prec(l_i) = T(l_i)\setminus \bigcup_{j\prec i} T(l_j)$; then $\{P_\prec(l_i)\}_{i\in[n]}$ is a partition of $V(\mathcal N)$ and each $P_\prec(l_i)$ is a directed path ending at $l_i$.

An **ordered tree-path decomposition** of an arbitrary phylogenetic network is a pair $(\prec,\{P(l_i)\}_{i\in[n]})$ where $\prec$ is a total order on $[n]$, the $P(l_i)$ partition the vertices into directed paths ending at $l_i$, and the remaining arcs ("bridges") run from a vertex of some $P(l_i)$ to the maximal (first) vertex of a path $P(l_k)$ with $i \prec k$ (the precise conditions are Definition 16 of the source).

**Theorem.** A phylogenetic network $\mathcal N$ is tree-child if and only if it admits an ordered tree-path decomposition. For a tree-child network, every tree-path order $\prec$ gives the decomposition $(\prec,\{P_\prec(l_i)\})$.

## Expansion

Two tree-paths ending at the same vertex are nested, because a tree vertex has a unique parent; hence a tree-path from $u$ to $v$ is the unique directed path between them. Walking up from a leaf through tree vertices stops exactly at the root or at a reticulation, which gives the maximal tree-path $T(l)$, and the tree-child property guarantees every vertex has a tree-vertex descendant chain down to some leaf, so the $T(l)$ cover $V$. Removing earlier paths in a tree-path order leaves suffixes that are still directed paths, so they partition $V$. Conversely, given a decomposition, each non-leaf vertex has its successor on its own path as a child with in-degree 1 (bridges only enter maximal vertices of later paths), so every inner vertex has a tree child. The decomposition is a structural certificate rather than a test: tree-childness is already a local check. It recovers the network once the bridges are specified and is the combinatorial skeleton translated into vector conditions for μ-representations.

## Sources

- T. Fuentes, V. Moulton, K. T. Huber, J. C. Pons, "Characterization of tree-child networks in terms of mu vectors", arXiv:2609.25177 (2026), Section 3 (Lemma 7, Corollary 8, Propositions 12, 14, 15, Definitions 13 and 16, Theorem 18), <https://doi.org/10.48550/arXiv.2609.25177>.
