# Level-3 bound for non-binary unrooted tree-based networks

**Setting.** An **unrooted phylogenetic network** on a finite set $X$ is a connected simple graph with no degree-two vertices whose degree-one vertices (leaves) are bijectively labelled by $X$; it is binary if every inner vertex has degree $3$. It is **tree-based** if it has a spanning tree whose leaf set is exactly $X$ (a support tree). A *blob* is a maximal connected subgraph without cut edges, and a network is **proper** if removing any cut edge or cut vertex leaves components that each contain a leaf. Tree-basedness is defined for connected multigraphs in the same way, with leaf set the vertices of degree at most one. A network is **level-$k$** if at most $k$ edges must be removed from each blob to obtain a tree. For a blob $B$, the simple network $B_N$ is $B$ together with the cut edges of $N$ incident with $B$.

**Basic results (binary or not).**

- Every unrooted tree-based network is proper (Lemma 2); this generalizes the binary statement that every cut edge of a tree-based network induces a split of $X$.
- $N$ is tree-based if and only if $B_N$ is tree-based for every blob $B$ of $N$ (Proposition 2).
- If $|X|\ge2$ and $N-x$ (delete leaf $x$ and suppress the resulting degree-two vertex) is tree-based, then $N$ is tree-based (Lemma 3); the converse fails even for binary networks with one blob.
- If $N$ is level-$k$ with $k\ge2$ and $B$ is a non-trivial blob incident with at most two cut edges, then $3<|V(B)|\le2k$ (Lemma 4).

**Lemma 5.** Every minimal (in the number of vertices) proper unrooted non-binary network that is not tree-based has $6$ interior vertices and $2$ leaves, so $8$ vertices in total.

**Theorem 1.** Every proper unrooted non-binary phylogenetic network of level at most $3$ is tree-based. Unrooted non-binary networks of level greater than $3$ need not be tree-based: there is a proper level-$4$ network on two leaves with $8$ vertices that is not tree-based.

By contrast, every proper unrooted *binary* network of level at most $4$ is tree-based, so allowing higher vertex degrees lowers the guaranteed level by one.

## Expansion

By the blob decomposition and the leaf-deletion lemma it suffices to treat simple networks with two leaves, where tree-basedness means a Hamiltonian path between the two attachment points through all inner vertices. Level-$1$ blobs lose at most one edge per blob, which never creates new leaves. For level $2$, the blob bound gives at most $4$ blob vertices, below the $8$-vertex threshold of Lemma 5. Lemma 5 and the level-$3$ case are settled by exhaustive search over all simple graphs with at most $8$ vertices (House of Graphs): $28$ proper networks with up to $7$ vertices are all tree-based, and among the $197$ proper networks on $8$ vertices exactly $8$ are not tree-based, none of level $3$. The level-$4$ counterexample forces any Hamiltonian $x$–$y$ path through a vertex that leaves one of two symmetric vertices unreachable.

## Sources

- Mareike Fischer, Michelle Galla, Lina Herbst, Yangjing Long and Kristina Wicke, "Unrooted non-binary tree-based phylogenetic networks", arXiv (2018), Section 3.1 "Basic results" (Lemmas 2–4, Proposition 2) and Section 3.2 "Unrooted non-binary tree-based networks" (Theorem 1, Lemma 5), <https://doi.org/10.48550/arXiv.1810.06853> Published version: Discrete Applied Mathematics 294 (2021) 10–30, <https://doi.org/10.1016/j.dam.2021.01.005>.
