# Dichotomy for unions of conjunctive queries on tuple-independent probabilistic databases

For every Boolean union of conjunctive queries $Q$ (equivalently, positive existential first-order sentence),
computing $p(Q)$ on tuple-independent probabilistic databases is either in polynomial time in the size of the database
or $\#P$-hard. The polynomial-time cases are exactly the queries whose ranked, lineage-equivalent form is safe, that is,
evaluable by repeatedly applying inclusion–exclusion (skipping the terms whose Möbius function in the query's CNF
lattice vanishes) and eliminating a separator variable.

## Expansion

This node states the dichotomy; the characterization of the tractable side needs pages for ranked queries,
lineage reductions, separator variables, the CNF lattice with its Möbius function, and the rewriting that defines
unsafe queries (the source's Sections 2–4).

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [Positive relational algebra = unions of conjunctive queries = positive existential calculus](../relational-calculus/positive-relational-algebra-unions-of-conjunctive-queries-po.md)

## Proof depends on

- [The non-hierarchical query R(x), S(x, y), T(y) is #P-hard](the-query-h0-is-sharp-p-hard.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of probabilistic inference for unions of conjunctive queries", *Journal of the ACM*, 2012; authors' manuscript <https://homes.cs.washington.edu/~suciu/jacm-dichotomy.pdf>, the abstract, Definition 4.14, Theorem 4.21 and Theorem 4.5.
