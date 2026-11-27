# Deadlock-freedom of Petri nets is decidable

There is an algorithm that decides, given an ordinary Petri net $(N, M_0)$, whether it is [deadlock-free](../liveness-and-deadlock-freedom.md): deadlock-freedom reduces in polynomial time to reachability. For a net that is [connected](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md) and has at least one place and one transition, the reduction is the composition of the two reductions linked below.

## Depends on

- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Place/transition Petri nets](../place-transition-petri-nets.md)
- [Connected and strongly connected nets](../state-machines-marked-graphs-and-free-choice-nets/connected-and-strongly-connected-nets.md)

## Proof depends on

- [Deadlock-freedom reduces to reaching a marking empty on a set of places](deadlock-freedom-reduces-to-emptying-a-set-of-places.md)
- [Reaching a marking empty on a set of places reduces to reachability](emptying-a-set-of-places-reduces-to-reachability.md)
- [Reachability in Petri nets is decidable](../reachability-is-decidable.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Section 3.2.3, paragraph "Deadlock-freedom", Theorems 3.2.25 and 3.2.26, pp. 66–69.
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 3, paragraph "Deadlock-freedom" (the polynomial-time reduction to reachability for all Petri nets), p. 7.
