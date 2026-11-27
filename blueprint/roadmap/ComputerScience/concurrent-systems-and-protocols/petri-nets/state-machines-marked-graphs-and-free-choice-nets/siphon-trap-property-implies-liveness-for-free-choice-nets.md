# The siphon–trap property implies liveness for free-choice nets

Let $(N, M_0)$ be a net that is [extended free-choice](extended-free-choice-nets.md) and whose net is [connected](connected-and-strongly-connected-nets.md) and has at least one place and one transition. If every [siphon](../siphons-and-traps.md) of $N$ contains a trap marked at $M_0$, then $(N, M_0)$ is [live](../liveness-and-deadlock-freedom.md).

## Depends on

- [Extended free-choice nets](extended-free-choice-nets.md)
- [Siphons and traps](../siphons-and-traps.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)

## Proof depends on

- [Marked traps stay marked](../invariants-siphons-and-traps/marked-traps-stay-marked.md)
- [Unmarked siphons stay unmarked](../invariants-siphons-and-traps/unmarked-siphons-stay-unmarked.md)

## Expansion

This page becomes ready once the rest of its proof is linked:

- if the net is not live, some reachable marking $M$ makes every transition either live or dead at $M$, with at least one dead, because live and dead transitions stay so and a transition that is neither can be made dead (proof prerequisite)
- in an extended free-choice net, every transition $t$ dead at $M$ has an input place unmarked at $M$ all of whose input transitions are dead at $M$, and the places selected in this way, one for each dead transition, form a siphon unmarked at $M$; the set of all places unmarked at $M$ need not be a siphon (proof prerequisite)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.3.3 ("First part of Commoner's Liveness Theorem") with its proof, pp. 105–107.
