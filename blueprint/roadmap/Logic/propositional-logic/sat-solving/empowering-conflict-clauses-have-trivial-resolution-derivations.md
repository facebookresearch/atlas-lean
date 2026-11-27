# Empowering conflict clauses have trivial resolution derivations

Let $S = (\Delta, \Gamma, D)$ be a normal 1-inconsistent [SAT state](unit-resolution-and-sat-solver-states.md) and $C$ a [conflict clause](conflict-clauses-and-asserting-clauses.md) of $S$ that is [1-empowering](empowering-and-1-provable-clauses.md) with respect to $\Delta \wedge \Gamma$. Then some clause $C' \subseteq C$ has a trivial resolution derivation from $\Delta \wedge \Gamma$. Since its resolved variables are distinct, that derivation has $O(n)$ steps for $n$ variables.

**Proof sketch.** Write $C = \alpha \vee \ell$ with $\ell$ its empowering literal. Deciding the negations of the literals of $\alpha$ and then $\neg \ell$ makes unit resolution reach a conflict, and the decision learning scheme then returns a clause $C'$ of negated decision literals, so $C' \subseteq C$. A trivial resolution derivation of $C'$ starts from the clause that unit resolution made false and resolves, in the reverse of the order in which the literals were implied, with the clause that implied each non-decision literal still present; each implied variable is resolved at most once, and the last resolvent contains only negated decision literals. The source cites Beame, Kautz and Sabharwal (2004, Proposition 4) for this step.

## Depends on

- [Unit resolution and SAT-solver states](unit-resolution-and-sat-solver-states.md)
- [Conflict clauses and asserting clauses](conflict-clauses-and-asserting-clauses.md)
- [Empowering and 1-provable clauses](empowering-and-1-provable-clauses.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers with restarts", revised version of the paper in *Principles and Practice of Constraint Programming (CP 2009)*, LNCS 5732, Springer, 2009, pp. 654–668, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 4, Proposition 3 and the remark after it, with its proof in Appendix A; Section 3.1 assumes every SAT state normal.
