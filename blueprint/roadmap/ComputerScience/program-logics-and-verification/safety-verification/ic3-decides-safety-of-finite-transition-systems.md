# IC3 decides safety of finite transition systems

For a finite transition system $(I, T)$ and a set $P$ of safe states, the IC3 (property-directed reachability) procedure terminates, and it either returns an inductive invariant $F \supseteq I$ with $F \subseteq P$ and $\mathrm{Img}_T(F) \subseteq F$, proving that every reachable state is in $P$, or returns a finite path from an initial state to a state outside $P$. Termination uses the [frame invariants](frame-invariants-of-ic3.md): as long as no two consecutive frames are equal, $F_0 \subsetneq F_1 \subsetneq \dots \subsetneq F_{k-1}$ is a strictly increasing chain of sets of states, so the number of frames is bounded by the number of states plus one; and between two additions of a frame each blocking step removes at least one state from a frame, so there are finitely many of them.

## Depends on

- [Satisfiability of a CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Proof depends on

- [Safety by inductive invariants](safety-by-inductive-invariants.md)
- [Frame invariants of IC3](frame-invariants-of-ic3.md)

## Sources

- A. R. Bradley, "SAT-based model checking without unrolling", *VMCAI 2011*, LNCS 6538, Springer, 2011
