# Liveness of marked graphs

A [marked graph](subclasses-of-petri-nets.md) $(G, M_0)$ is [live](liveness-and-deadlock-freedom.md) if and only if $M_0$ places at least one token on each directed circuit of $G$.

## Depends on

- [State machines, marked graphs and free-choice nets](subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)

## Proof depends on

- [Token count on circuits of a marked graph is invariant](token-count-on-circuits-of-marked-graphs.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B: Theorem 7 and the argument before it, which back-tracks token-free arcs from a transition that is never enabled to a token-free circuit.
