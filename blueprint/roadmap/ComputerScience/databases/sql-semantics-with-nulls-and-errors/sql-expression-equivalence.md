# Equivalence of SQL expressions is a congruence

Call expressions $e_1, e_2$ **equivalent** in context $\Gamma$ if on every row conforming to $\Gamma$ both fail or both succeed with the same datum (which error is raised is not observed, since strict evaluation fixes one of the evaluation orders SQL permits). This is an equivalence relation and a congruence for every expression constructor; it is compatible with renaming and with replacing substituted expressions by equivalent ones; and substituting into equivalent expressions preserves equivalence provided the substituted expressions are safe and have the column types. The side condition is necessary: $\mathsf{TRUE}$ and $x\ \mathsf{IS\ NULL\ OR}\ x\ \mathsf{IS\ NOT\ NULL}$ are equivalent, but substituting $1/0$ for $x$ makes only the second fail.

## Depends on

- [Resolved SQL expressions and their evaluation](resolved-sql-expressions.md)
- [Typing and safety of SQL expressions](sql-expression-typing-and-safety.md)

## Proof depends on

- [Type soundness and safety for SQL expressions](sql-type-soundness.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
