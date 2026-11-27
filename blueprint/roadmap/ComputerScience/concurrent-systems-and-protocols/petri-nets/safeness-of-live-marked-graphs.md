# Safeness of live marked graphs

A [live](liveness-and-deadlock-freedom.md) [marked graph](subclasses-of-petri-nets.md) $(G, M_0)$ is [safe](boundedness-and-safeness.md) if and only if every arc (place) of $G$ belongs to a directed circuit $C$ with $M_0(C) = 1$. More generally, an arc is bounded, that is, holds a bounded number of tokens over the markings reachable in $(G, M_0)$, if and only if it lies on some directed circuit of $G$; an arc on no directed circuit is unbounded. For a bounded arc, the maximum number of tokens it holds over the reachable markings is the minimum of $M_0(C)$ over the directed circuits $C$ containing it.

## Depends on

- [State machines, marked graphs and free-choice nets](subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)

## Proof depends on

- [Token count on circuits of a marked graph is invariant](token-count-on-circuits-of-marked-graphs.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B: Theorems 8 and 9.
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.2.4 and Corollary 5.2.5(1)–(2), p. 99, stated for live T-systems, that is, live marked graphs whose net is connected; a live marked graph is the disjoint union of its connected components, each a live marked graph, so the statement holds componentwise.
