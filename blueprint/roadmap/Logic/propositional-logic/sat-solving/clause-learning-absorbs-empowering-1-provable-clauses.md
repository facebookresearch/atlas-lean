# Clause learning absorbs empowering 1-provable clauses

Let $\Delta$ be a CNF formula with $n$ variables and $C$ a clause that is [1-empowering and 1-provable](empowering-and-1-provable-clauses.md) with respect to $\Delta$. For every asserting learning scheme AS there is an extended branching sequence $\sigma$ such that the run of [CLR](clause-learning-as-a-proof-system.md) with AS on $\Delta$ along $\sigma$ ends with a knowledge base that absorbs $C$, producing a resolution derivation of size $O(n^4)$.

## Depends on

- [Empowering and 1-provable clauses](empowering-and-1-provable-clauses.md)
- [Clause learning as a proof system](clause-learning-as-a-proof-system.md)

## Sources

- K. Pipatsrisawat and A. Darwiche, "On the power of clause-learning SAT solvers as resolution engines", *Artificial Intelligence* 175(2):512–525, 2011, <http://reasoning.cs.ucla.edu/fetch.php?id=101&type=pdf>, Section 4, Proposition 2 and footnote 7 (the bound on the size of the derivation), with its proof in Section 5.
