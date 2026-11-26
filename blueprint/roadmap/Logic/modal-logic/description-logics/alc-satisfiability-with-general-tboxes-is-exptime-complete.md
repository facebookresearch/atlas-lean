# ALC satisfiability with respect to general TBoxes is EXPTIME-complete

The problem of deciding whether an ALC concept is satisfiable with respect to a TBox, in the sense of [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md), where the TBox is an arbitrary finite set of general concept inclusions $C \sqsubseteq D$, is complete for [EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md), deterministic exponential time, under [polynomial-time many-one reductions](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md). The same holds for general terminological axioms $C \doteq D$, which are pairs of inclusions; a TBox has the same models as the single axiom $\hat C \doteq \top$, where $\hat C$ is the conjunction of the concepts $\neg C \sqcup D$ over its inclusions.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [The class EXP](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/exp.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Expansion

The cited survey states this result and refers to K. Schild, "Terminological cycles and the propositional μ-calculus", KR 1994, for the proof. A good expansion checks that source and adds its prerequisites: the translation of ALC with general TBoxes into propositional dynamic logic or the modal μ-calculus, the EXPTIME upper bound for the target logic, and the hardness reduction, together with the tableau algorithm with subset blocking described in the survey.

## Sources

- F. Baader and U. Sattler, "An overview of tableau algorithms for description logics", *Studia Logica* 69(1):5–40, 2001, <https://lat.inf.tu-dresden.de/research/papers/2001/BaaderSattler-StudiaLogica.pdf>, Section 5, terminological axioms and reasoning with respect to TBoxes, p. 15, and Section 5.2, the reduction to $\hat C \doteq \top$, blocking for general TBoxes and the statement that satisfiability with respect to general terminological axioms is EXPTIME-complete for ALC, pp. 17–19.
