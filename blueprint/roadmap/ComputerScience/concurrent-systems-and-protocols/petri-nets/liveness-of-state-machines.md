# Liveness and safeness of state machines

Let $(N, M_0)$ be a [state machine](subclasses-of-petri-nets.md).

1. $(N, M_0)$ is [live](liveness-and-deadlock-freedom.md) if and only if $N$ is strongly connected and $M_0$ has at least one token.
2. $(N, M_0)$ is [safe](boundedness-and-safeness.md) if and only if $M_0$ has at most one token; a live state machine is safe if and only if $M_0$ has exactly one token.

## Depends on

- [State machines, marked graphs and free-choice nets](subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B: Theorems 4 and 5.
