# Bounded places of live marked graphs

Let $(N, M_0)$ be a [live](../liveness-and-deadlock-freedom.md) [marked graph](../subclasses-of-petri-nets.md). A place of $N$ is bounded, that is, has a bound on its number of tokens over all reachable markings, if and only if it lies on some directed circuit; and $(N, M_0)$ is [bounded](../boundedness-and-safeness.md) if and only if $N$ is strongly connected.

## Depends on

- [State machines, marked graphs and free-choice nets](../subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)

## Proof depends on

- [Safeness of live marked graphs](../safeness-of-live-marked-graphs.md)
- [Token count on circuits of a marked graph is invariant](../token-count-on-circuits-of-marked-graphs.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.2.4 ("Boundedness Theorem") and Corollary 5.2.5, items 1 and 3, p. 99.
