# Edgebased networks and generalized series-parallel graphs

**Setting.** An **unrooted phylogenetic network** on a finite set $X$ is a connected simple graph with no degree-two vertices whose degree-one vertices (leaves) are bijectively labelled by $X$; it is binary if every inner vertex has degree $3$. It is **tree-based** if it has a spanning tree whose leaf set is exactly $X$ (a support tree). A *blob* is a maximal connected subgraph without cut edges, and a network is **proper** if removing any cut edge or cut vertex leaves components that each contain a leaf. Graphs below may have parallel edges and loops. The *restriction operations* are: delete a leaf, suppress a degree-two vertex, delete one copy of a parallel edge, delete a loop. The *leaf shrink graph* $\mathcal{LS}(G)$ of a connected graph $G$ with at least two leaves applies restriction operations while more than two vertices remain, then removes parallel edges and loops on the last two vertices. $G$ (or a proper network $N$ with $|X|\ge2$) is **edgebased** if $\mathcal{LS}(G)$ is a single edge $K_2$. A connected loopless graph is a **generalized series-parallel (GSP)** graph if it reduces to $K_2$ by the first three operations.

**Theorems.**

1. A connected graph $G$ is a GSP graph if and only if it is loopless and can be reduced to $K_2$ by all four restriction operations; equivalently, if and only if it is loopless and edgebased. Since GSP graphs are recognized in linear time, edgebasedness of a network is decidable in linear time.
2. If $G$ is edgebased, then *every* sequence of restriction operations following the leaf shrinking procedure ends at $K_2$; the order of operations does not matter.
3. A proper unrooted phylogenetic network with at least two leaves that is edgebased is tree-based. The converse fails.
4. A proper unrooted network with at least two leaves is edgebased if and only if every non-trivial blob is edgebased.
5. Every proper unrooted binary network with at least two leaves whose underlying graph is chordal is edgebased, hence tree-based.

Recognizing tree-based unrooted networks is NP-complete in general, so edgebasedness is a linear-time certificate for a subclass.

## Expansion

Deleting a loop can always be avoided: the first loop created in a reduction comes from suppressing a degree-two endpoint of a parallel edge, and deleting that parallel copy first gives a loop-free reduction, which proves the equivalence with GSP graphs. A connected graph is GSP if and only if each block is series-parallel, so an edgebased network decomposes into series-parallel blocks; each such block has a spanning path-like tree between its terminals whose leaves are attachment points, and these glue into a support tree. A GSP graph can be reduced to any of its edges (a known theorem on GSP graphs), which allows a cut edge between two edgebased halves to serve as the common terminal edge in the blob decomposition. In a binary chordal blob every vertex lies in a triangle; suppressing a degree-two vertex of a triangle creates a parallel edge whose deletion again leaves a chordal graph with a degree-two vertex, and repeating this reduces the blob to one edge.

## Sources

- Mareike Fischer, Michelle Galla, Lina Herbst, Yangjing Long and Kristina Wicke, "Classes of treebased networks", arXiv (2018), Section 2 (definition of GSP graphs and the block lemma) and Section 3.2.1 "Edgebased networks" (relationship between edgebased and GSP graphs, order of restriction operations, edgebasedness implies treebasedness, blob reduction) and the binary chordal theorem of Section 3.2.2, <https://doi.org/10.48550/arXiv.1810.06844> Published version: Visual Computing for Industry, Biomedicine, and Art 3 (2020) 12, <https://doi.org/10.1186/s42492-020-00043-z>.
