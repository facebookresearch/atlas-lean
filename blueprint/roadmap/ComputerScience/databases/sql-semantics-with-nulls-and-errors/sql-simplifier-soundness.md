# A sound proof-producing SQL simplifier

Consider the bottom-up simplifier that folds operators on literals (never folding an error), pushes $\mathsf{NOT}$ into comparisons and null tests, removes double negation of booleans and integers, simplifies $\mathsf{AND}$/$\mathsf{OR}$ with boolean constants (absorbing to a constant only when the other operand is a safe predicate), removes additive and multiplicative identities on integers (but not $x \cdot 0$, which is $\mathsf{NULL}$ when $x$ is), rewrites $e\ \mathsf{IN}\ ()$ and singleton lists, eliminates $\mathsf{CASE}$ with a literal condition, and at the query level merges and pushes down selections under the safety conditions of the selection laws. Then every expression is equivalent to its simplification on every conforming row, and every query is ordered-equivalent to its simplification on every conforming instance; in particular simplification never turns a failing query into a succeeding one or conversely.

## Depends on

- [Equivalence of SQL expressions is a congruence](sql-expression-equivalence.md)
- [Three levels of SQL query equivalence and their congruence](sql-query-equivalence-levels.md)

## Proof depends on

- [Selection laws under strict evaluation](sql-selection-laws.md)
- [Equivalence of SQL expressions is a congruence](sql-expression-equivalence.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
