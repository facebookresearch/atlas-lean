# Live free-choice nets have the siphon–trap property

Let $(N, M_0)$ be a net that is [extended free-choice](extended-free-choice-nets.md), whose net is connected and has at least one transition. If $(N, M_0)$ is [live](../liveness-and-deadlock-freedom.md), then every [siphon](../siphons-and-traps.md) of $N$ contains a trap marked at $M_0$.

## Depends on

- [Extended free-choice nets](extended-free-choice-nets.md)
- [Siphons and traps](../siphons-and-traps.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Proof depends on

- [Live Petri nets mark every siphon initially](../invariants-siphons-and-traps/live-nets-mark-every-siphon.md)
- [Circuit-free allocations avoiding the maximal trap](circuit-free-allocations-avoiding-the-maximal-trap.md)
- [Allocation lemma for live free-choice nets](allocation-lemma-for-free-choice-nets.md)
- [Marked traps stay marked](../invariants-siphons-and-traps/marked-traps-stay-marked.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definition 1.3.8 (p. 16) and Theorem 5.3.9 ("Second half of Commoner's Liveness Theorem") with its proof, pp. 110–111.
