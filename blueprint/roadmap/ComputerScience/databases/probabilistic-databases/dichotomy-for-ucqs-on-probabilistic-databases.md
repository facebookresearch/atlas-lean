# Dichotomy for unions of conjunctive queries on tuple-independent probabilistic databases

For every Boolean union of conjunctive queries $Q$ (equivalently, positive existential first-order sentence), let
$Q'$ be a ranked query lineage-equivalent to $Q$. If $Q'$ is safe, computing $p(Q)$ on tuple-independent probabilistic
databases takes polynomial time in the size of the database; if $Q'$ is unsafe, the problem is $\#P$-hard. Here $Q'$
is unsafe when some sequence of the source's rewrite rules turns it into an immediately unsafe query, and safe
otherwise. Inclusion–exclusion over the query's CNF lattice (skipping terms whose Möbius function vanishes) and
elimination of a separator variable are two of the steps of the evaluation algorithm on safe queries, alongside
independent joins and unions and ground base cases; they are not by themselves the safety test.

## Expansion

This node states the dichotomy; the characterization of the tractable side needs pages for ranked queries,
lineage equivalence, separator variables, the CNF lattice with its Möbius function, the rewrite rules and the
immediately unsafe queries that define unsafe queries (the source's Definitions 4.4 and 4.14 and Sections 2–4).

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)

## Proof depends on

- [The non-hierarchical query R(x), S(x, y), T(y) is #P-hard](the-query-h0-is-sharp-p-hard.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of probabilistic inference for unions of conjunctive queries", *Journal of the ACM* 59(6), Article 30, 2012, with theorem numbers as in the authors' copy <https://homes.cs.washington.edu/~suciu/jacm-dichotomy.pdf>: the abstract, Definition 4.4, Definition 4.14, Theorem 4.21 and Theorem 4.5.
