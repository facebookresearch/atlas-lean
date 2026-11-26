# Clause learning p-simulates general resolution

For every asserting learning scheme LS, the [proof system](clause-learning-as-a-proof-system.md) $\mathrm{CLR}_{\mathrm{LS}}$ of clause learning with restarts p-simulates general resolution. In particular, clause learning with the first-UIP scheme does. Moreover, the extended branching sequence that realizes the simulation can be constructed in time polynomial in the sizes of the given refutation and formula.

**Proof sketch.** As long as the knowledge base is 1-consistent, a [refutation contains a clause that is 1-empowering and 1-provable](refutations-contain-an-empowering-1-provable-clause.md) with respect to it, which [clause learning can absorb](clause-learning-absorbs-empowering-1-provable-clauses.md) with polynomially many steps. Absorbed clauses stay absorbed, so after at most as many rounds as there are clauses in the refutation the knowledge base is 1-inconsistent. Each learned clause has a subclause with a [short trivial resolution derivation](empowering-conflict-clauses-have-trivial-resolution-derivations.md) from the knowledge base, which is what the refutation of $\mathrm{CLR}_{\mathrm{LS}}$ uses.

## Depends on

- [Clause learning as a proof system](clause-learning-as-a-proof-system.md)

## Proof depends on

- [Refutations contain an empowering 1-provable clause](refutations-contain-an-empowering-1-provable-clause.md)
- [Clause learning absorbs empowering 1-provable clauses](clause-learning-absorbs-empowering-1-provable-clauses.md)
- [Empowering conflict clauses have trivial resolution derivations](empowering-conflict-clauses-have-trivial-resolution-derivations.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers with restarts", revised version of the paper in *Principles and Practice of Constraint Programming (CP 2009)*, LNCS 5732, Springer, 2009, pp. 654–668, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 5: Theorem 1, Corollary 1 (first UIP), the proof sketch and the proof of Theorem 1, and Theorem 2 (polynomial-time construction of the branching sequence).
