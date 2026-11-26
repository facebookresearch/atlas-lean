# With distinct weights every MOE lies in every MST

If the edge weights of $G$ are pairwise distinct, then every fragment $S$ has a unique MOE $e_S$, and $e_S$ belongs to every minimum spanning tree of $G$.

## Proof sketch

If an MST $T$ omitted $e_S$, the exchange of the blue rule would strictly decrease the weight, because the crossing edge $e'$ of $T$ is heavier than $e_S$.

## Depends on

- [Minimum-weight outgoing edges of a vertex set](minimum-weight-outgoing-edge.md)

## Proof depends on

- [The blue rule: adding an MOE preserves extendability to an MST](blue-rule.md)

## Sources

- R. G. Gallager, P. A. Humblet and P. M. Spira, "A Distributed Algorithm for Minimum-Weight Spanning Trees", ACM Transactions on Programming Languages and Systems 5(1), 1983.
