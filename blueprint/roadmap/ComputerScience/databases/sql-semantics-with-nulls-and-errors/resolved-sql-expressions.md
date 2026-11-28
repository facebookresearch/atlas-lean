# Resolved SQL expressions and their evaluation

A **resolved expression** over $n$ columns is built from literals, typed $\mathsf{NULL}$, column references by position $\mathsf{col}\ i$ with $i < n$, the scalar operators, $e\ \mathsf{IN}$ (literal list), and $\mathsf{CASE\ WHEN}\ c\ \mathsf{THEN}\ a\ \mathsf{ELSE}\ b$. Evaluation on a row is strict and left to right: every operand is evaluated and the first error is the result, except that $\mathsf{CASE}$ evaluates only the branch it takes. **Renaming** reindexes columns and **substitution** replaces column $i$ by an expression $\sigma_i$. Column names are metadata resolved to positions beforehand: a reference $[q.]\mathit{name}$ resolves to the unique matching position, or fails as unknown or ambiguous. Constants, $\mathsf{NULL}$ and names are the terms of Guagliardo and Libkin's basic SQL (Figure 2); the scalar operators, $\mathsf{CASE}$, literal $\mathsf{IN}$-lists and runtime errors extend it and are not part of their semantics.

## Proof sketch

Substitution commutes with evaluation, by structural induction on the expression: evaluating a substituted expression equals evaluating the original on the row of results of $\sigma$, provided every $\sigma_i$ succeeds.

## Depends on

- [Strict semantics of SQL scalar operators](sql-scalar-operator-semantics.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
