# Kosaraju's algorithm computes the strongly connected components in condensation order

**Kosaraju's algorithm** computes the decreasing finishing order $\pi$ of a depth-first search of $G$, builds the transpose graph $G^\top$, and runs depth-first searches in $G^\top$ from the vertices in the order $\pi$, each search from a not yet visited vertex producing one component. The components produced are exactly the strongly connected components of $G$, and they are listed in a topological order of the condensation: if $G$ has an edge from a vertex of the $i$-th component to a vertex of the $j$-th component, then $i \le j$.

## Proof sketch

The vertex with the latest finishing time lies in a source component of the condensation; in $G^\top$ that component is a sink, so the search from it visits exactly that component. Removing it and repeating gives the claim by induction.

## Depends on

- [SCC partition](../strongly-connected-components/is-sccpartition.md)
- [Acyclic condensation](../strongly-connected-components/condensation-acyclic.md)
- [Transpose of a directed adjacency graph](../adjacency-list/transpose.md)
- [Whole-graph decreasing finish order](../depth-first-search/decreasing-finish-all.md)

## Sources

- M. Sharir, "A Strong-Connectivity Algorithm and its Applications in Data Flow Analysis", Computers & Mathematics with Applications 7(1), 1981.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
