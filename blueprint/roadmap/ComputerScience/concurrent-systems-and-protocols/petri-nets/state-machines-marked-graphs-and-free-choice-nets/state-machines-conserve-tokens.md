# State machines conserve the number of tokens

Let $(N, M_0)$ be a [state machine](../subclasses-of-petri-nets.md) whose net is [connected](connected-and-strongly-connected-nets.md) and has at least one place and one transition, with places $P$. Every marking $M$ reachable from $M_0$ satisfies $M(P) = M_0(P)$, where $M(P) = \sum_{s \in P} M(s)$.

## Depends on

- [State machines, marked graphs and free-choice nets](../subclasses-of-petri-nets.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 5.1.1 (S-nets and S-systems) and Proposition 5.1.2 ("Fundamental property of S-systems"), p. 96.
