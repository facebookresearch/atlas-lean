# SQL values, NULL and typed rows

The SQL column types are $\mathsf{int}$ (unbounded integers), $\mathsf{text}$ and $\mathsf{bool}$. A **value** is a non-null element of one of these types; a **datum** (cell content) is either a value or $\mathsf{NULL}$, and $\mathsf{NULL}$ belongs to every type. A row of an $n$-column table is a function $\mathrm{Fin}\,n \to \text{Datum}$, so columns are referenced by position; a **typing context** is $\Gamma : \mathrm{Fin}\,n \to \text{Type}$, and a row **conforms** to $\Gamma$ if each cell is $\mathsf{NULL}$ or a value of its column's type. The row of a join is the concatenation of the input rows, and it conforms to the concatenated context exactly when both parts conform. A **database schema** names tables with arities and column types; an **instance** assigns each table a bag (list) of rows, and **conforms** when all its rows do.

## Depends on

- [Databases conforming to a schema](../relational-algebra/conforms.md)
- [SQL nulls and three-valued logic](../bags-and-nulls/sql-nulls-and-three-valued-logic.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- E. F. Codd, "A Relational Model of Data for Large Shared Data Banks", Communications of the ACM 13(6), 1970.
