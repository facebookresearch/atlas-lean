# Empowering and 1-provable clauses

Let $\Delta$ be a CNF formula and $\alpha \Rightarrow \ell$ a clause, $\alpha$ the conjunction of the negations of its other literals. The clause is *1-empowering* with respect to $\Delta$, with *empowering literal* $\ell$, if $\Delta \models (\alpha \Rightarrow \ell)$, $\Delta \wedge \alpha$ is 1-consistent, and unit resolution does not derive $\ell$ from $\Delta \wedge \alpha$ (see [unit resolution](unit-resolution-and-sat-solver-states.md)). A clause implied by $\Delta$ that is not 1-empowering is *absorbed* by $\Delta$. A clause $C$ is *1-provable* with respect to $\Delta$ if $\Delta \wedge \neg C \vdash \mathrm{false}$ by unit resolution.

A subsuming clause absorbs the clauses it subsumes, adding clauses to $\Delta$ never turns an absorbed clause into a 1-empowering one, and every [asserting clause](conflict-clauses-and-asserting-clauses.md) is 1-empowering with respect to the knowledge base at the time it is derived, with its asserted literal as empowering literal.

## Depends on

- [Unit resolution and SAT-solver states](unit-resolution-and-sat-solver-states.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers as resolution engines", *Artificial Intelligence* 175(2):512–525, 2011, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 4: Definition 6 (1-empowerment), Definition 7 (1-provability), and the remarks after Definition 6.
