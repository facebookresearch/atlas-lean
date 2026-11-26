# Safeness of live marked graphs

A [live](liveness-and-deadlock-freedom.md) [marked graph](subclasses-of-petri-nets.md) $(G, M_0)$ is [safe](boundedness-and-safeness.md) if and only if every arc (place) of $G$ belongs to a directed circuit $C$ with $M_0(C) = 1$. More generally, for an arc that lies on some directed circuit of $G$, the maximum number of tokens it holds over the markings reachable in $(G, M_0)$ is the minimum of $M_0(C)$ over the directed circuits $C$ containing it.

## Depends on

- [State machines, marked graphs and free-choice nets](subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)

## Proof depends on

- [Token count on circuits of a marked graph is invariant](token-count-on-circuits-of-marked-graphs.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B: Theorems 8 and 9.
