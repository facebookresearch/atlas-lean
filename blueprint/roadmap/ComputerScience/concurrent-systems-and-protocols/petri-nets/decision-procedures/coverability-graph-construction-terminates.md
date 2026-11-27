# The coverability graph construction terminates

For every ordinary Petri net $(N, M_0)$ whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, the [coverability graph algorithm](coverability-graph-algorithm.md) terminates, so the coverability graph of $(N, M_0)$ is finite.

## Depends on

- [The coverability graph algorithm](coverability-graph-algorithm.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [König's lemma for finitely branching graphs](konig-s-lemma-for-finitely-branching-graphs.md)
- [Dickson's lemma for finite products of well-quasi-orders](dickson-s-lemma.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 3.2.5 and its proof (König's lemma, the stabilization of the set of ω-places along an infinite path, and Dickson's lemma on the normal places), p. 52.
