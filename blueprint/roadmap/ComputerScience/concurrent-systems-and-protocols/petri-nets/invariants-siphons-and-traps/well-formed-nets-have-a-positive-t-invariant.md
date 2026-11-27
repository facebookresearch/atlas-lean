# Well-formed nets have a positive T-invariant

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition. $N$ is *well formed* if some marking $M_0$ makes $(N, M_0)$ [live](../liveness-and-deadlock-freedom.md) and [bounded](../boundedness-and-safeness.md). Every well-formed net has a T-invariant $J$ with $J(t) > 0$ for every transition $t$ (see [T-invariants and reproducing firing sequences](t-invariants-and-reproducing-sequences.md)).

## Depends on

- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)
- [T-invariants and reproducing firing sequences](t-invariants-and-reproducing-sequences.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 2.10.3 (p. 38) and Theorem 4.3.17 with its proof (p. 90).
