# Reachability in live marked graphs

Let $(N, M_0)$ be a [live](../liveness-and-deadlock-freedom.md) [marked graph](../subclasses-of-petri-nets.md) whose net is [connected](connected-and-strongly-connected-nets.md) and has at least one place and one transition. A marking $M$ of $N$ is reachable from $M_0$ if and only if $M \sim M_0$, that is, $M$ and $M_0$ [agree on all S-invariants](../invariants-siphons-and-traps/agreement-on-all-s-invariants.md).

## Depends on

- [State machines, marked graphs and free-choice nets](../subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Agreement of markings on all S-invariants](../invariants-siphons-and-traps/agreement-on-all-s-invariants.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Proof depends on

- [T-invariants of connected marked graphs](t-invariants-of-marked-graphs.md)
- [Token count on circuits of a marked graph is invariant](../token-count-on-circuits-of-marked-graphs.md)
- [Liveness of marked graphs](../liveness-of-marked-graphs.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.2.7 ("Reachability Theorem") with its proof, pp. 100–101.
