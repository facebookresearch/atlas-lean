# Non-hierarchical conjunctive queries are #P-hard on probabilistic databases

If a Boolean conjunctive query $q$ (self-joins allowed) is not hierarchical, then computing its probability $p(q)$ on
tuple-independent probabilistic databases is $\#P$-hard.

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [Hierarchical conjunctive queries](hierarchical-conjunctive-queries.md)
- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)

## Proof depends on

- [The non-hierarchical query R(x), S(x, y), T(y) is #P-hard](the-query-h0-is-sharp-p-hard.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of conjunctive queries on probabilistic structures", *Proceedings of the 26th ACM Symposium on Principles of Database Systems (PODS)*, 2007, pp. 293–302, Theorem 1.4 (p. 294).
- N. Dalvi and D. Suciu, "The dichotomy of probabilistic inference for unions of conjunctive queries", *Journal of the ACM*, 2012; authors' manuscript <https://homes.cs.washington.edu/~suciu/jacm-dichotomy.pdf>, Proposition 8.8 (every non-hierarchical forbidden query is $h_0$).
