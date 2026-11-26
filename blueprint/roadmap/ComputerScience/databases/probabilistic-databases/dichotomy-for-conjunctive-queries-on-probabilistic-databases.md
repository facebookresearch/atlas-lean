# Dichotomy for conjunctive queries on tuple-independent probabilistic databases

For every Boolean conjunctive query $q$ (self-joins allowed), computing $p(q)$ on tuple-independent probabilistic
databases is either in polynomial time or $\#P$-complete. Every non-hierarchical query is $\#P$-hard; a hierarchical
query is $\#P$-hard if it has an inversion without erasers, and is in polynomial time if all its inversions have
erasers.

## Expansion

This node states the dichotomy precisely; the boundary inside hierarchical queries uses the source's notions of
unifiers, inversions and erasers (its Section 2), which need pages of their own before the second sentence can be
checked clause by clause.

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [Hierarchical conjunctive queries](hierarchical-conjunctive-queries.md)
- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Non-hierarchical conjunctive queries are #P-hard on probabilistic databases](non-hierarchical-conjunctive-queries-are-sharp-p-hard.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of conjunctive queries on probabilistic structures", *Proceedings of the 26th ACM Symposium on Principles of Database Systems (PODS)*, 2007, pp. 293–302, Theorem 1.1 (p. 293) and Theorem 1.8.
