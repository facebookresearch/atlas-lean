# Three levels of SQL query equivalence and their congruence

Say $q_1 \equiv_\ell q_2$ at level $\ell \in \{\text{ordered}, \text{bag}, \text{set}\}$ if on every conforming instance both fail or both succeed with results that are equal as lists (ordered), equal up to permutation (bag), or equal as sets (set). Ordered equivalence implies bag equivalence, which implies set equivalence, and each is an equivalence relation. Every query constructor is a congruence at every level in its query arguments, and in its expression arguments for expression equivalence in the typing context of its (well-typed) input; set-equivalent inputs give bag-equivalent $\mathsf{DISTINCT}$.

## Depends on

- [SQL queries with bag semantics and strict evaluation](sql-query-bag-semantics.md)
- [Query equivalence](../relational-algebra/equiv.md)

## Proof depends on

- [Equivalence of SQL expressions is a congruence](sql-expression-equivalence.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
