# Empowering and 1-provable clauses

Let $\Delta$ be a CNF formula and $\alpha \Rightarrow \ell$ a clause, $\alpha$ the conjunction of the negations of its other literals. The clause is *1-empowering* with respect to $\Delta$, with *empowering literal* $\ell$, if $\Delta \models (\alpha \Rightarrow \ell)$, $\Delta \wedge \alpha$ is 1-consistent, and unit resolution does not derive $\ell$ from $\Delta \wedge \alpha$ (see [unit resolution](unit-resolution-and-sat-solver-states.md)). A clause implied by $\Delta$ that is not 1-empowering is *absorbed* by $\Delta$. A clause $C$ is *1-provable* with respect to $\Delta$ if $\Delta \wedge \neg C \vdash \mathrm{false}$ by unit resolution.

A subsuming clause absorbs the clauses it subsumes, adding clauses to $\Delta$ never turns an absorbed clause into a 1-empowering one, and every [asserting clause](conflict-clauses-and-asserting-clauses.md), a clause of a normal state with $|D| > 0$, is 1-empowering with respect to the knowledge base at the time it is derived, with its asserted literal as empowering literal: its other literals are false on the trail at levels at most the assertion level $m < |D|$, so unit resolution from the knowledge base and their negations derives only literals that $D_m$ already gives, a set that is 1-consistent because the state is normal and $m < |D|$, without either literal of the asserted variable, which the trail assigns only at level $|D|$.

## Depends on

- [Conflict clauses and asserting clauses](conflict-clauses-and-asserting-clauses.md)
- [Unit resolution and SAT-solver states](unit-resolution-and-sat-solver-states.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers with restarts", revised version of the paper in *Principles and Practice of Constraint Programming (CP 2009)*, LNCS 5732, Springer, 2009, pp. 654–668, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 4: Definition 6 (1-empowerment), Definition 7 (1-provability), and the remarks after Definition 6, which state that every asserting clause is 1-empowering at the time of its derivation, citing earlier work of the authors; the justification from the assignment trail is written out here.
