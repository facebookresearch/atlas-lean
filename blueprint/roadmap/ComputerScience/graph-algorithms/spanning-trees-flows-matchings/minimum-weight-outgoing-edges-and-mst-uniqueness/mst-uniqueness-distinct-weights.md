# Distinct edge weights give a unique minimum spanning tree

If $G$ is a finite connected simple graph whose edge weights are pairwise distinct, then $G$ has exactly one minimum spanning tree. This uniqueness is what makes fragment-merging algorithms such as Borůvka's and the distributed Gallager-Humblet-Spira algorithm well defined: all fragments merging along their MOEs in any order build the same tree.

## Proof sketch

Every edge of an MST $T$ is the MOE of one side of the cut obtained by deleting it from $T$, hence lies in every MST; two spanning trees with $T \subseteq T'$ are equal.

## Depends on

- [Minimum-weight outgoing edges of a vertex set](minimum-weight-outgoing-edge.md)

## Proof depends on

- [With distinct weights every MOE lies in every MST](moe-in-every-mst.md)

## Sources

- R. G. Gallager, P. A. Humblet and P. M. Spira, "A Distributed Algorithm for Minimum-Weight Spanning Trees", ACM Transactions on Programming Languages and Systems 5(1), 1983.
- R. E. Tarjan, "Data Structures and Network Algorithms", SIAM, 1983.
