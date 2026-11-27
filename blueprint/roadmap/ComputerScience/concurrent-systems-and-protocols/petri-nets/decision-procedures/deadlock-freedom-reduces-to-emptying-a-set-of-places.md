# Deadlock-freedom reduces to reaching a marking empty on a set of places

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, with places $P$ and transitions $T$, and let $\mathcal{S}$ be the finite family of sets $R \subseteq P$ that contain at least one input place of every transition. A marking is dead if and only if the set of places it leaves unmarked belongs to $\mathcal{S}$. So $(N, M_0)$ is [deadlock-free](../liveness-and-deadlock-freedom.md) if and only if, for no $R \in \mathcal{S}$, some marking reachable from $M_0$ puts no token on any place of $R$; and deadlock-freedom is decidable whenever it is decidable whether some reachable marking is empty on a given set of places.

## Depends on

- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, the problem P and Theorem 3.2.25 with its proof (facts (1) and (2)), pp. 66–67.
