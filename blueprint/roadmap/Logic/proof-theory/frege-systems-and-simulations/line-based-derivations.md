# Line-based (dag-like) derivations

Fix a set of lines (formulas, clauses or inequalities), a set of hypotheses and a set of rules, each rule deriving a line from finitely many premises. A *line-based derivation* is a finite sequence of lines in which every line is a hypothesis, an axiom instance, or follows from earlier lines by a rule; a line may be used as a premise any number of times, so the derivation is a directed acyclic graph rather than a tree. Its size is its number of lines. Derivations compose: a derivation whose hypotheses are derived by earlier derivations combines into one derivation whose size is the sum.

## Depends on

- [Cook–Reckhow propositional proof systems](../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Sources

- S. A. Cook and R. A. Reckhow, "The Relative Efficiency of Propositional Proof Systems", The Journal of Symbolic Logic 44(1), 36–50, 1979: Section 1 (derivations, number of lines $\lambda(\pi)$).
- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997.
