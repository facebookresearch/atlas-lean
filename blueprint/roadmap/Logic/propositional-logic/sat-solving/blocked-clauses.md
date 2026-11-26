# Blocked clauses

Let $F$ be a CNF formula. A clause $C$ is *blocked* by a literal $p \in C$ with respect to $F$ if every resolvent of $C$ upon $p$ with a clause of $F$ containing $\bar p$ is a tautology. A blocked clause is a [RAT](../proof-certificates/rup-and-rat-clauses.md) on its blocking literal, since unit propagation on the negation of a tautology reaches a conflict at once.

## Depends on

- [RUP and RAT clauses](../proof-certificates/rup-and-rat-clauses.md)

## Sources

- B. Kiesl, A. Rebola-Pardo, M. J. H. Heule and A. Biere, "Simulating strong practical proof systems with extended resolution", *Journal of Automated Reasoning* 64:1247–1267, 2020, <https://cca.informatik.uni-freiburg.de/papers/KieslRebolaPardoHeuleBiere-JAR20.pdf>, Section 5: Definition 7 (blocked clauses) and the remark that every blocked clause is a RAT.
- M. Järvisalo, A. Biere and M. Heule, "Blocked clause elimination", in *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2010)*, LNCS 6015, Springer, 2010, pp. 129–144, <https://fmv.jku.at/papers/JarvisaloBiereHeule-TACAS10.pdf>, Section 4: Definitions 1 and 2 (blocking literals and blocked clauses).
