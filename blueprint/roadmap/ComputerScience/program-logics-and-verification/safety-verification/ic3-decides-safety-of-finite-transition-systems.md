# IC3 decides safety of finite transition systems

For a finite transition system $(I, T)$ and a set $P$ of safe states, the IC3 (property-directed reachability) procedure terminates, and it either returns an inductive invariant $F \supseteq I$ with $F \subseteq P$ and $\mathrm{Img}_T(F) \subseteq F$, proving that every reachable state is in $P$, or returns a finite path from an initial state to a state outside $P$.

## Depends on

- [Satisfiability of a CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnfsat.md)

## Proof depends on

- [Safety by inductive invariants](safety-by-inductive-invariants.md)

## Sources

- A. R. Bradley, "SAT-based model checking without unrolling", *VMCAI 2011*, LNCS 6538, Springer, 2011
