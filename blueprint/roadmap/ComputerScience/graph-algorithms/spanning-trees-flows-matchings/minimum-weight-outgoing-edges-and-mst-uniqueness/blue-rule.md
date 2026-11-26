# The blue rule: adding an MOE preserves extendability to an MST

Let $F$ be an edge set contained in some MST of $G$, let $S$ be a vertex set such that no edge of $F$ has exactly one endpoint in $S$ (for instance a connected component of $(V, F)$), and let $e$ be an MOE of $S$. Then $F \cup \{e\}$ is contained in some MST of $G$.

## Proof sketch

If an MST $T \supseteq F$ omits $e$, the cycle of $T + e$ crosses the cut $(S, V \setminus S)$ at another edge $e'$, which is not in $F$; $T + e - e'$ is a spanning tree of weight at most $w(T)$.

## Depends on

- [Minimum-weight outgoing edges of a vertex set](minimum-weight-outgoing-edge.md)

## Proof depends on

- [Kruskal's greedy cut property](../kruskal-s-algorithm/kruskal-greedy-cut-property.md)

## Sources

- R. E. Tarjan, "Data Structures and Network Algorithms", SIAM, 1983.
- R. G. Gallager, P. A. Humblet and P. M. Spira, "A Distributed Algorithm for Minimum-Weight Spanning Trees", ACM Transactions on Programming Languages and Systems 5(1), 1983.
