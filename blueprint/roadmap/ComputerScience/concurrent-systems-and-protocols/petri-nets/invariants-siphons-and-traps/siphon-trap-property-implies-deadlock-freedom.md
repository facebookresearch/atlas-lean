# The siphon–trap property implies deadlock-freedom

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) whose net is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition. If every [siphon](../siphons-and-traps.md) of $N$ contains a trap that is marked at $M_0$, then $(N, M_0)$ is [deadlock-free](../liveness-and-deadlock-freedom.md).

## Depends on

- [Siphons and traps](../siphons-and-traps.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [The unmarked places of a dead marking form a siphon](unmarked-places-of-a-dead-marking-form-a-siphon.md)
- [Marked traps stay marked](marked-traps-stay-marked.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Proposition 4.4.10 with its proof, p. 93.
