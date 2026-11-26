# Typing and safety of SQL expressions

The **type** of an expression over a typing context $\Gamma$ is computed compositionally: literals have their value's type, $\mathsf{NULL}$ its declared type, $\mathsf{col}\ i$ the type $\Gamma(i)$, operators by their typing rules, $e\ \mathsf{IN}\ vs$ is boolean when all list elements have $e$'s type, and $\mathsf{CASE}$ needs a boolean condition and branches of equal type. An expression is **division-safe** if every $/$ and $\%$ has a nonzero integer literal as divisor, and **safe** if it is well typed and division-safe (a decidable syntactic check); a **safe predicate** is a safe boolean expression.

## Depends on

- [Resolved SQL expressions and their evaluation](resolved-sql-expressions.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
