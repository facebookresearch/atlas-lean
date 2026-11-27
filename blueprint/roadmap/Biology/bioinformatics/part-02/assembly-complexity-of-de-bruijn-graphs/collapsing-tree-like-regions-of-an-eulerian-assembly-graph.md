# Collapsing tree-like regions of an Eulerian assembly graph

Let $G$ be a connected Eulerian directed multigraph (every vertex has in-degree equal to out-degree), for instance a de Bruijn graph of a circular genome. Decompose the edge set of $G$ into edge-disjoint simple cycles $C_1, \dots, C_m$ (each cycle visits every vertex at most once), and form the **cycle graph** $\mathrm{cycle}(G)$ with one vertex per $C_i$ and an edge between $C_i$ and $C_j$ whenever they share a vertex of $G$.

**Facts.**

1. If $\mathrm{cycle}(G)$ is a tree, then all Eulerian circuits of $G$ spell the same cyclic word: $G$ has a single Eulerian tour up to the choice of start.
2. More generally, if the subgraph of $\mathrm{cycle}(G)$ induced by a set of cycles is a tree, the corresponding region of $G$ is traversed in the same way by every Eulerian tour, so it can be replaced by a single vertex labelled with the sequence of that unique traversal without changing the set of words consistent with $G$.

A **forward decision vertex** has one predecessor and several successors, a **backward decision vertex** has several predecessors and one successor, and a **full decision vertex** has both several predecessors and several successors. Splitting a forward decision vertex $v$ with predecessor $u$ and successors $w_1,\dots,w_m$ into copies $v_1,\dots,v_m$ (with $u \to v_i \to w_i$ carrying the multiplicities of $v \to w_i$) also preserves the set of spelled words. After repeated path compression, tree collapsing, splitting of half-decision vertices, and conversion of non-decision vertices into labelled edges, the graph is a single vertex or every remaining vertex is a full decision vertex, and the remaining edges spell maximal unambiguous contigs whose lengths sum to the genome length.

**Multiplicity forcing.** If $u \to v$ has the largest multiplicity $c_u$ among edges into $v$, $v \to w$ has the largest multiplicity $c_w$ among edges out of $v$, $u \ne w$, and $c_u > d^+(v) - c_w$, then the path $u \to v \to w$ occurs in every Eulerian tour (pigeonhole).

## Depends on

- [Hutchinson–Wilf count of words consistent with a de Bruijn graph](hutchinson-wilf-count-of-words-consistent-with-a-de-bruijn-graph.md)
- [Euler circuit criterion for directed multigraphs](../../../../ComputerScience/graph-algorithms/traversal-and-connectivity/hierholzer-s-algorithm-for-euler-circuits/exists-is-euler-circuit-iff.md)

## Expansion

An Eulerian tour entering a region whose cycles are arranged as a tree must, at each shared vertex, finish the hanging cycle before returning, because the tree structure leaves no alternative re-entry; so the traversal order inside the region is forced. Algorithmically the region is collapsed leaf by leaf: a vertex $v$ whose only predecessor and only successor is $u$, with $u$ otherwise having one in- and one out-edge, is merged into $u$, as are self-loops at a vertex with one non-loop in- and out-edge. These reductions give the smallest equivalent graph used to measure assembly complexity and idealized N50 contig sizes.

## Sources

- C. Kingsford, M. C. Schatz and M. Pop, "Assembly complexity of prokaryotic genomes using short reads", BMC Bioinformatics 11 (2010), 21, Methods ("Compressing tree-like regions", "Splitting half decision nodes", "Exploiting edge multiplicities", "Maximal compression"), <https://doi.org/10.1186/1471-2105-11-21>, PMCID: PMC2821320.
