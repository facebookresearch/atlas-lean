# Conflict clauses and asserting clauses

Let $S = (\Delta, \Gamma, D)$ be a 1-inconsistent [SAT state](unit-resolution-and-sat-solver-states.md) with an assignment trail. A clause $\alpha = \ell_1 \vee \dots \vee \ell_m$ is a *conflict clause* of $S$ if $\Delta \wedge \Gamma \wedge \neg\alpha \vdash \mathrm{false}$ by unit resolution, and each $\ell_i$ is false on the trail. A conflict clause is *asserting* if exactly one of its literals, the *asserted literal*, is false at level $|D|$; its *assertion level* is the largest implication level below $|D|$ of its other literals, or $0$ if it has one literal. Falsity is read off the trail, not off unit-resolution derivability: with $\Delta = \{p,\ \bar a \vee u,\ \bar a \vee \bar u \vee \bar p\}$ and the decision $a$, unit resolution derives $\bar p$ and $a$, the complements of both literals of $p \vee \bar a$, but $p \vee \bar a$ is not a conflict clause, since $p$ is true on the trail; that clause is already absorbed by $\Delta$ and asserts nothing. A *learning scheme* maps each normal 1-inconsistent state with a nonempty decision sequence and its trail, the states at which clause learning learns, to a conflict clause, and it is *asserting* if it always returns an asserting clause; the first-UIP scheme is asserting. At a 1-inconsistent state with no decision there is no literal to assert, and clause learning reports unsatisfiability there without learning.

A *trivial resolution derivation* is a [resolution derivation](../resolution-size-and-width/is-resolution-derivation.md) without weakening in which every step after the first resolves the last resolvent with a clause of the knowledge base, and the resolved variables are pairwise distinct.

## Depends on

- [Unit resolution and SAT-solver states](unit-resolution-and-sat-solver-states.md)
- [Resolution derivation](../resolution-size-and-width/is-resolution-derivation.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers with restarts", revised version of the paper in *Principles and Practice of Constraint Programming (CP 2009)*, LNCS 5732, Springer, 2009, pp. 654–668, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 3.1: Definition 3 (conflict clauses, whose negated literals are among the implications and decisions discovered by unit resolution in the state), the notion of trivial resolution derivation, and Definition 4 (asserting clauses and assertion level); Section 3.2 (learning schemes, asserting learning schemes, the first-UIP scheme). That falsity and levels are read off one assignment trail is written out here.
