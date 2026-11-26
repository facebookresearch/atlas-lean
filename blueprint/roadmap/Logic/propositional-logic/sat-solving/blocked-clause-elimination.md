# Blocked clause elimination

Let $F$ be a CNF formula and call a clause of $F$ blocked if some literal [blocks it](blocked-clauses.md) with respect to $F$.

1. Removing a blocked clause from $F$ preserves satisfiability.
2. If $C \in F$ is blocked with respect to $F$, then every other clause of $F$ blocked with respect to $F$ is blocked with respect to $F \setminus \{C\}$.
3. Consequently *blocked clause elimination*, removing blocked clauses until none is left, is confluent: its result does not depend on the order of removals.

## Depends on

- [Blocked clauses](blocked-clauses.md)

## Proof depends on

- [Adding a RAT clause preserves satisfiability](adding-a-rat-clause-preserves-satisfiability.md)

## Sources

- M. Järvisalo, A. Biere and M. Heule, "Blocked clause elimination", in *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2010)*, LNCS 6015, Springer, 2010, pp. 129–144, <https://fmv.jku.at/papers/JarvisaloBiereHeule-TACAS10.pdf>, Section 4: Definitions 1 and 2 (blocking literals and blocked clauses), Proposition 2 (removal preserves satisfiability, due to Kullmann), Proposition 3 and Proposition 4 (confluence).
