# ALC ABox consistency is PSPACE-complete

Deciding whether an ALC ABox is consistent with respect to the empty TBox, in the sense of [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md), is complete for [PSPACE](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md) under [polynomial-time many-one reductions](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md); consequently the instance problem for ALC without a TBox is PSPACE-complete as well.

**Proof idea.** Apply the tableau rules first only to the individuals of the input ABox (pre-completion), then forget the role assertions and test, for each individual, the conjunction of its concept assertions for satisfiability in polynomial space. Hardness follows from that of concept satisfiability, as $C$ is satisfiable exactly when the ABox $\{C(a)\}$ is consistent.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [ALC concept satisfiability is PSPACE-complete](alc-concept-satisfiability-is-pspace-complete.md)
- [Tableau algorithm for ALC](alc-tableau-algorithm.md)

## Sources

- F. Baader and U. Sattler, "An overview of tableau algorithms for description logics", *Studia Logica* 69(1):5–40, 2001, <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSattler-StudiaLogica.pdf>, Section 2, the reduction of concept satisfiability to ABox consistency, p. 6, and Section 3.2, the pre-completion argument and Theorem 3, p. 10.
