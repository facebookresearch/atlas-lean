# Allocation lemma for live free-choice nets

Let $(N, M_0)$ be a [live](../liveness-and-deadlock-freedom.md) net that is [extended free-choice](extended-free-choice-nets.md) and whose net is [connected](connected-and-strongly-connected-nets.md) and has at least one place and one transition, let $\mathcal{C}$ be a nonempty set of [clusters](clusters-of-a-net.md) and $\alpha$ an [allocation](allocations-of-clusters.md) of $\mathcal{C}$. There is an infinite firing sequence from $M_0$ that contains infinitely many occurrences of allocated transitions and no occurrence of a transition of $\bigcup_{c \in \mathcal{C}} c \setminus \{\alpha(c)\}$.

## Depends on

- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Extended free-choice nets](extended-free-choice-nets.md)
- [Allocations of clusters](allocations-of-clusters.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Lemma 5.3.8 ("Allocation Lemma") with its proof, p. 110.
