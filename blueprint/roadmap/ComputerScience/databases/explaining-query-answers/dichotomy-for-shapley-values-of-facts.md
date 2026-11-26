# Dichotomy for Shapley values of facts for self-join-free Boolean conjunctive queries

**Theorem (Livshits, Bertossi, Kimelfeld and Sebag).** Let $q$ be a Boolean conjunctive query without self-joins. If $q$ is
[hierarchical](../probabilistic-databases/hierarchical-conjunctive-queries.md), then the [Shapley value](shapley-value-of-a-database-fact.md)
$\mathrm{Shapley}(D, q, f)$ can be computed in time polynomial in $D$, given $D$ and an endogenous fact $f$. Otherwise the problem
is $\mathrm{FP}^{\#\mathrm{P}}$-complete: as hard as every function computable in polynomial time with a
[$\#\mathrm{P}$](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-p.md) oracle.

## Depends on

- [Shapley value of a database fact](shapley-value-of-a-database-fact.md)
- [Hierarchical conjunctive queries](../probabilistic-databases/hierarchical-conjunctive-queries.md)
- [The counting class $\#P$](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-p.md)

## Sources

- E. Livshits, L. Bertossi, B. Kimelfeld and M. Sebag, "The Shapley value of tuples in query answering", *Logical Methods in Computer Science* 17(3) (2021) 22; conference version ICDT 2020; arXiv:1904.08679 <https://arxiv.org/abs/1904.08679>, Theorem 4.1, with the tractable side in Theorem 4.3 and the hardness side in Section 4.1.2.
