# Commoner's theorem for free-choice nets

Let $(N, M_0)$ be a [free-choice net](subclasses-of-petri-nets.md) whose net is connected and has at least one transition. Then $(N, M_0)$ is [live](liveness-and-deadlock-freedom.md) if and only if every [siphon](siphons-and-traps.md) of $N$ contains a trap that is marked at $M_0$. Both hypotheses, which the survey leaves implicit, are needed for the forward direction: a place with no arcs that is unmarked at $M_0$ is a siphon containing no marked trap, whatever the rest of the net does, and the net consisting of one unmarked place and no transitions is connected and vacuously live.

## Depends on

- [State machines, marked graphs and free-choice nets](subclasses-of-petri-nets.md)
- [Siphons and traps](siphons-and-traps.md)
- [Liveness and deadlock-freedom of Petri nets](liveness-and-deadlock-freedom.md)
- [Connected and strongly connected nets](state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [Extended free-choice nets](state-machines-marked-graphs-and-free-choice-nets/extended-free-choice-nets.md)
- [The siphon–trap property implies liveness for free-choice nets](state-machines-marked-graphs-and-free-choice-nets/siphon-trap-property-implies-liveness-for-free-choice-nets.md)
- [Live free-choice nets have the siphon–trap property](state-machines-marked-graphs-and-free-choice-nets/live-free-choice-nets-have-the-siphon-trap-property.md)

## Sources

- T. Murata, "Petri nets: Properties, analysis and applications", *Proceedings of the IEEE* 77(4):541–580, 1989, Section VI-B, Theorem 12 (stated without proof, with Example 9).
- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 1.3.8 (Petri nets are connected, with nonempty sets of places and transitions) and Theorems 5.3.3 and 5.3.9 (Commoner's liveness theorem), pp. 16 and 105–111.
