# Conflict clauses and asserting clauses

Let $S = (\Delta, \Gamma, D)$ be a 1-inconsistent [SAT state](unit-resolution-and-sat-solver-states.md). A clause $\alpha = \ell_1 \vee \dots \vee \ell_m$ is a *conflict clause* of $S$ if $\Delta \wedge \Gamma \wedge \neg\alpha \vdash \mathrm{false}$ by unit resolution, and $S \vdash \neg\ell_i$ for each $i$. A conflict clause is *asserting* if exactly one of its literals, the *asserted literal*, has implication level $|D|$; its *assertion level* is the largest implication level below $|D|$ of its other literals, or $0$ if it has one literal. A *learning scheme* maps each 1-inconsistent state to a conflict clause, and it is *asserting* if it always returns an asserting clause; the first-UIP scheme is asserting.

A *trivial resolution derivation* is a resolution derivation in which every step after the first resolves the last resolvent with a clause of the knowledge base, and the resolved variables are pairwise distinct.

## Depends on

- [Unit resolution and SAT-solver states](unit-resolution-and-sat-solver-states.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers as resolution engines", *Artificial Intelligence* 175(2):512–525, 2011, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 3.1: Definition 3 (conflict clauses), the notion of trivial resolution derivation, and Definition 4 (asserting clauses and assertion level); Section 3.2 (learning schemes, asserting learning schemes, the first-UIP scheme).
