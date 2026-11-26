# Selection laws under strict evaluation

For well-typed inputs, the following ordered equivalences hold with the stated safety conditions: (i) $\mathsf{WHERE}\ p$ over $\mathsf{WHERE}\ c$ equals $\mathsf{WHERE}\ (c\ \mathsf{AND}\ p)$ when $p$ is a safe predicate; (ii) two selections commute when both are safe; (iii) a selection over a projection moves below it with the projection substituted into the predicate when the projection is safe; (iv) a selection over a join whose predicate mentions only one input's columns pushes into that input when it and the join predicate are safe; (v) a selection over a cross join is the inner join with that predicate; and $\mathsf{WHERE\ TRUE}$ is the identity. Each safety condition is necessary: dropping it gives instances on which one side fails and the other succeeds.

## Proof sketch

A safe predicate never fails, so filtering by it is a pure filter and the classical bag-algebra identities apply; without safety, changing the set of rows on which a predicate is evaluated changes whether an error is raised.

## Depends on

- [Three levels of SQL query equivalence and their congruence](sql-query-equivalence-levels.md)
- [Selection pushdown into the left operand of a join](../relational-algebra/select-join-left.md)
- [Selections commute](../relational-algebra/select-comm.md)

## Proof depends on

- [Type soundness and safety for SQL expressions](sql-type-soundness.md)
- [Equivalence of SQL expressions is a congruence](sql-expression-equivalence.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- S. Abiteboul, R. Hull and V. Vianu, "Foundations of Databases", Addison-Wesley, 1995.
