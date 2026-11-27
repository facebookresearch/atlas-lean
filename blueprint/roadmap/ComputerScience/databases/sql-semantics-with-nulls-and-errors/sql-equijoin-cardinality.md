# Equijoin cardinality equals the join size of non-null keys

For queries $q_1, q_2$ and key columns $i$ of $q_1$ and $j$ of $q_2$ of a common type $\tau$, on a conforming instance on which both succeed, the number of rows of $q_1\ \mathsf{JOIN}\ q_2\ \mathsf{ON}\ q_1.i = q_2.j$ equals

$$
\sum_{a} \mathrm{cnt}_a(K_1) \cdot \mathrm{cnt}_a(K_2),
$$

where $K_1$, $K_2$ are the lists of non-null key values of the two results and $\mathrm{cnt}_a$ counts occurrences of $a$. $\mathsf{NULL}$ keys match nothing, since $\mathsf{NULL} = \mathsf{NULL}$ is $\mathsf{unknown}$; counting with structural equality of data gives the same result when one input has no $\mathsf{NULL}$ key. This is the join size estimated by second-moment sketches in streaming.

## Depends on

- [SQL queries with bag semantics and strict evaluation](sql-query-bag-semantics.md)

## Proof depends on

- [SQL truth values form Kleene's strong three-valued logic](sql-kleene-truth-values.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- N. Alon, Y. Matias and M. Szegedy, "The Space Complexity of Approximating the Frequency Moments", Journal of Computer and System Sciences 58(1), 1999.
