# Live Petri nets mark every siphon initially

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) that is connected and has at least one transition. If $(N, M_0)$ is [live](../liveness-and-deadlock-freedom.md), then $M_0$ puts a token on some place of every [siphon](../siphons-and-traps.md) of $N$. Without a transition, a single unmarked place is a connected, vacuously live net with an unmarked siphon.

## Depends on

- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Siphons and traps](../siphons-and-traps.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [Unmarked siphons stay unmarked](unmarked-siphons-stay-unmarked.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Proposition 4.4.4 with its proof (using connectedness and the nonempty set of transitions of Definition 1.3.8), pp. 16 and 92.
