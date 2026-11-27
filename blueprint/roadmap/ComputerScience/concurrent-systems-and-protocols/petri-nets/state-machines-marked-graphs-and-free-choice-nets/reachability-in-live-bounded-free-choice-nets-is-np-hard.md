# Reachability in live and bounded free-choice nets is NP-hard

The problem that asks, given a [live](../liveness-and-deadlock-freedom.md) and [bounded](../boundedness-and-safeness.md) net $(N, M_0)$ that is [extended free-choice](extended-free-choice-nets.md) and a marking $M$, whether $M$ is reachable from $M_0$, is NP-hard.

## Depends on

- [Extended free-choice nets](extended-free-choice-nets.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [Boundedness and safeness of Petri nets](../boundedness-and-safeness.md)
- [Reachability set and reachability graph](../reachability-set-and-reachability-graph.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Cook–Levin theorem: SAT is NP-complete](../../../../TheoryOfComputation/np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.3.16 with its proof, a reduction from satisfiability through the modules of Figures 5.7–5.9, pp. 115–117.
