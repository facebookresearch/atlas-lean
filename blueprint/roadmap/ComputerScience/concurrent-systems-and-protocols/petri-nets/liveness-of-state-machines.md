# Liveness and safeness of state machines

Let $(N, M_0)$ be a [state machine](subclasses-of-petri-nets.md) whose net is connected and has at least one place and one transition.

1. $(N, M_0)$ is [live](liveness-and-deadlock-freedom.md) if and only if $N$ is strongly connected and $M_0$ has at least one token.
2. If $M_0$ has at most one token, $(N, M_0)$ is [safe](boundedness-and-safeness.md), since every firing moves one token. A live state machine is safe if and only if $M_0$ has exactly one token.

The survey states the first part of 2 as an equivalence and leaves the hypotheses implicit; neither can be dropped. Two disjoint self-loops $s_i \to t_i \to s_i$ with one token each form a live and safe state machine that is not strongly connected and has two tokens. A connected state machine whose two marked places are sinks fed only from an unmarked place is safe with two tokens. A single place with no transitions and no token is vacuously live.

## Depends on

- [State machines, marked graphs and free-choice nets](subclasses-of-petri-nets.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](boundedness-and-safeness.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B: Theorems 4 and 5.
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 1.3.8 (Petri nets are connected, with nonempty sets of places and transitions), Proposition 5.1.2 and Theorems 5.1.3 and 5.1.4, pp. 16 and 96.
