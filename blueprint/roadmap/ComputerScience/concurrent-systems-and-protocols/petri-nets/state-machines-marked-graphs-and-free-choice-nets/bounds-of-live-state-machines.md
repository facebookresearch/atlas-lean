# Bounds of live state machines

Let $(N, M_0)$ be a [live](../liveness-and-deadlock-freedom.md) [state machine](../subclasses-of-petri-nets.md) with places $P$ and let $b \ge 0$. Then every place has at most $b$ tokens in every reachable marking if and only if $M_0(P) \le b$.

## Depends on

- [State machines, marked graphs and free-choice nets](../subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)

## Proof depends on

- [State machines conserve the number of tokens](state-machines-conserve-tokens.md)
- [Liveness and safeness of state machines](../liveness-of-state-machines.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.1.4 ("Boundedness Theorem"), p. 96.
