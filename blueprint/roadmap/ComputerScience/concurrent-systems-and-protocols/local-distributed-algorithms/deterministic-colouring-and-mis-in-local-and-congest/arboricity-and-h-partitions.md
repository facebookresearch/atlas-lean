# Arboricity and H-partitions

Let $G = (V, E)$ be a simple connected graph with $n$ vertices and maximum degree $\Delta$, whose vertices carry distinct identifiers from $\{1, \dots, n^{O(1)}\}$. The arboricity $a(G)$ is the minimum number of forests whose union is $E$; by the Nash-Williams theorem, for $n \ge 2$, $a(G) = \max_{H} \bigl\lceil \lvert E(H) \rvert / (\lvert V(H) \rvert - 1) \bigr\rceil$ over subgraphs $H$ with at least two vertices, while for $n = 1$ there is no such subgraph and $a(G) = 0$. For an integer $A \ge 1$ (typically $A = q\,a(G)$ with $q > 2$), an H-partition with degree bound $A$ is a partition $V = H_1 \sqcup \dots \sqcup H_\ell$ such that every vertex of $H_i$ has at most $A$ neighbours in $H_i \cup H_{i+1} \cup \dots \cup H_\ell$; orienting each edge from the lower-indexed (or, within a class, lower-identifier) endpoint yields an acyclic orientation with out-degree at most $A$.

## Depends on

- [Nash–Williams arboricity theorem](../../../../GraphTheory/graph-invariants-and-labelings/nash-williams-arboricity-theorem/nash-williams-arboricity.md)

## Sources

- L. Barenboim, M. Elkin, "Sublogarithmic distributed MIS algorithm for sparse graphs using Nash-Williams decomposition", Distributed Computing 22 (2010); PODC 2008.
