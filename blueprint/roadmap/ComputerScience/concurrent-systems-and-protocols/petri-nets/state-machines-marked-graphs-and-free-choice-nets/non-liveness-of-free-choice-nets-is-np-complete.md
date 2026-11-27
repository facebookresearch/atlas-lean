# Non-liveness of free-choice nets is NP-complete

The problem that asks, given a net $(N, M_0)$ that is [extended free-choice](extended-free-choice-nets.md) and whose net is connected and has at least one transition, whether $(N, M_0)$ is not [live](../liveness-and-deadlock-freedom.md) is NP-complete. Membership in NP guesses a [siphon](../siphons-and-traps.md) and checks in polynomial time that the largest trap it contains is unmarked at $M_0$; hardness is a reduction from satisfiability of Boolean formulas.

## Depends on

- [Extended free-choice nets](extended-free-choice-nets.md)
- [Liveness and deadlock-freedom of Petri nets](../liveness-and-deadlock-freedom.md)
- [NP-complete decision problems](../../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)
- [Connected and strongly connected nets](connected-and-strongly-connected-nets.md)
- [Siphons and traps](../siphons-and-traps.md)

## Proof depends on

- [The siphon–trap property implies liveness for free-choice nets](siphon-trap-property-implies-liveness-for-free-choice-nets.md)
- [Live free-choice nets have the siphon–trap property](live-free-choice-nets-have-the-siphon-trap-property.md)
- [Cook–Levin theorem: SAT is NP-complete](../../../../TheoryOfComputation/np-completeness/cook-levin/cook-levin-sat-np-complete.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Theorem 5.3.10 ("Complexity") with its proof and Figure 5.5, pp. 111–112.
