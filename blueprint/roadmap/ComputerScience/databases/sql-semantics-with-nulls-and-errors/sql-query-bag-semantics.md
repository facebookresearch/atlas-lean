# SQL queries with bag semantics and strict evaluation

A **query** over schema $S$ with $n$ output columns is a table, $\mathsf{WHERE}$ (selection by a predicate), a $\mathsf{SELECT}$ list (projection by $n$ expressions), an inner join $\mathsf{ON}\ \theta$ (a cross join is $\mathsf{ON\ TRUE}$), $\mathsf{UNION\ ALL}$, or $\mathsf{DISTINCT}$; output arities are part of the type, so a projection or predicate cannot mention a missing column. Evaluation on an instance returns a list of rows (a bag) or an error: projection, join and $\mathsf{UNION\ ALL}$ keep duplicates; $\mathsf{DISTINCT}$ removes them, treating rows with $\mathsf{NULL}$ in the same places as duplicates. Evaluation is strict: a predicate or projection is evaluated on every input row (pair, for joins) and the first error fails the whole query.

## Depends on

- [Resolved SQL expressions and their evaluation](resolved-sql-expressions.md)
- [Bag relations and bag relational algebra](../bags-and-nulls/bag-relations-and-bag-relational-algebra.md)
- [Relational algebra queries](../relational-algebra/expr.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- S. Abiteboul, R. Hull and V. Vianu, "Foundations of Databases", Addison-Wesley, 1995.
