# A universal factor of IID for the free uniform spanning forest

Code a simple graph on $\mathbb N$ by its symmetric Boolean adjacency matrix with false diagonal, and code each possible edge once by its sorted pair of distinct endpoints. There exists one Boolean edge-selection rule $\Phi(G,U,e)$, jointly Borel in graph code, real vertex labels, and edge, that commutes pointwise with all permutations of $\mathbb N$ acting on graphs, labels and edges together. It uses no distinguished vertex. For every connected locally finite such graph and every measurable vertex label family with independent uniform $[0,1]$ finite marginals, the output has the following law.

Take any increasing exhaustion by nonempty finite connected subgraphs of $G$ whose union contains every edge. For any finite sets $A,B$ of possible edges, the proportion of spanning trees in the exhaustion subgraph containing every edge of $A$ and no edge of $B$ converges to the probability that the output contains every edge of $A$ and no edge of $B$. The rule is measurable at every output edge. The input has arbitrary probability-space realization of the prescribed IID labels.

**Conventions.** Use standard Borel graph and edge codes, the product vertex-label law, exhaustion of the graph by finite connected subgraphs (not required to be induced), and free spanning-tree cylinder limits. Finite uniform laws do not identify boundary vertices.

## Depends on

- [Graph-coded free spanning-forest cylinder law](free-spanning-forest-cylinder-law.md)

## Expansion

The exhaustion-independent free forest law and a graph-uniform Borel sampling construction compatible with all relabellings, not only automorphisms of a particular transitive graph.

Separate existence and uniqueness from cylinder limits, then prove the universal factor construction and its pointwise covariance under relabelling. In the coding bridge include possible nonedges and incompatible finite prescriptions, which must have the same cylinder probabilities as in the finite limits.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FreeUniformSpanningForest.lean#L141-L144)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/231.md)
- [Accompanying manuscript: The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf)
