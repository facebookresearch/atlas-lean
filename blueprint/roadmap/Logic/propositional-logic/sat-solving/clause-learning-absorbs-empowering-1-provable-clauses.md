# Clause learning absorbs empowering 1-provable clauses

Let $\Delta$ be a CNF formula with $n$ variables and $C$ a clause that is [1-empowering and 1-provable](empowering-and-1-provable-clauses.md) with respect to $\Delta$. For every asserting learning scheme AS there is an extended branching sequence $\sigma$ such that the run of [CLR](clause-learning-as-a-proof-system.md) with AS on $\Delta$ along $\sigma$ ends with a knowledge base that absorbs $C$, producing a resolution derivation of size $O(n^4)$.

## Depends on

- [Empowering and 1-provable clauses](empowering-and-1-provable-clauses.md)
- [Clause learning as a proof system](clause-learning-as-a-proof-system.md)

## Proof depends on

- [Empowering conflict clauses have trivial resolution derivations](empowering-conflict-clauses-have-trivial-resolution-derivations.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers with restarts", revised version of the paper in *Principles and Practice of Constraint Programming (CP 2009)*, LNCS 5732, Springer, 2009, pp. 654–668, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 4, Proposition 2 and footnote 7 (the bound on the size of the derivation, which corrects the proceedings version), with its proof in Appendix A.
