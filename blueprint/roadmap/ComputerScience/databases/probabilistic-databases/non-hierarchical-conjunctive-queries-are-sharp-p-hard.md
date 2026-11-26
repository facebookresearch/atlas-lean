# Conjunctive queries whose minimal equivalent query is not hierarchical are #P-hard on probabilistic databases

Let $q$ be a Boolean conjunctive query (self-joins allowed) and $q_0$ a minimal conjunctive query equivalent to $q$.
If $q_0$ is not hierarchical (equivalently, the Boolean conjunctive property defined by $q$ is not hierarchical), then
computing $p(q)$ on tuple-independent probabilistic databases is $\#P$-hard. Testing $q$ itself is not enough: the
query $R(x, x), R(x, y), R(y, y)$ is not hierarchical, but it is equivalent to $\exists z\, R(z, z)$, whose probability
$1 - \prod_a \big(1 - p(R(a, a))\big)$ is computable in polynomial time.

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [Hierarchical conjunctive queries](hierarchical-conjunctive-queries.md)
- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)
- [Minimizations and cores of conjunctive queries](../conjunctive-queries/cores-and-minimization/minimizations-and-cores-of-conjunctive-queries.md)

## Proof depends on

- [The non-hierarchical query R(x), S(x, y), T(y) is #P-hard](the-query-h0-is-sharp-p-hard.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of conjunctive queries on probabilistic structures", *Proceedings of the 26th ACM Symposium on Principles of Database Systems (PODS)*, 2007, pp. 293–302, Definition 1.2 and Theorem 1.4 (p. 294), which is stated for conjunctive properties.
- N. Dalvi and D. Suciu, "The dichotomy of probabilistic inference for unions of conjunctive queries", *Journal of the ACM* 59(6), Article 30, 2012, with theorem numbers as in the authors' copy <https://homes.cs.washington.edu/~suciu/jacm-dichotomy.pdf>: Proposition 8.8 (every non-hierarchical forbidden query is $h_0$).
