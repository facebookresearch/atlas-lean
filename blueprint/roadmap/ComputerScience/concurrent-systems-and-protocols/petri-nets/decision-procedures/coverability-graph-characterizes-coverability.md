# The coverability graph characterizes coverable markings

Let $(N, M_0)$ be an ordinary Petri net whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, and $M$ a marking of $N$. There is a marking $M' \ge M$ reachable from $M_0$ if and only if the coverability graph of $(N, M_0)$, computed by the [coverability graph algorithm](coverability-graph-algorithm.md), contains an ω-marking $M'' \ge M$.

## Depends on

- [The coverability graph algorithm](coverability-graph-algorithm.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [ω-places of the coverability graph can be pumped](omega-places-of-the-coverability-graph-can-be-pumped.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 3.2.8 and its proof, p. 55.
