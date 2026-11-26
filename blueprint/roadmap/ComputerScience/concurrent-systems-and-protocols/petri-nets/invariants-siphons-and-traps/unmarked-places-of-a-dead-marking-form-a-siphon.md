# The unmarked places of a dead marking form a siphon

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) with at least one transition, and let $M$ be a dead marking of $N$, one at which no transition is enabled. Then the set of places unmarked at $M$ is a [siphon](../siphons-and-traps.md) of $N$. Consequently, if every marking reachable from $M_0$ marks every siphon of $N$, then $(N, M_0)$ is [deadlock-free](../liveness-and-deadlock-freedom.md).

## Depends on

- [Siphons and traps](../siphons-and-traps.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Proposition 4.4.5 with its proof and Corollary 4.4.6, p. 92.
