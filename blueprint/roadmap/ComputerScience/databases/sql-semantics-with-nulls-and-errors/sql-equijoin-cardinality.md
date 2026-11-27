# Equijoin cardinality equals the join size of non-null keys

For queries $q_1, q_2$ and key columns $i$ of $q_1$ and $j$ of $q_2$ of a common type $\tau$, on a conforming instance on which both succeed, the number of rows of $q_1\ \mathsf{JOIN}\ q_2\ \mathsf{ON}\ q_1.i = q_2.j$ equals

$$
\sum_{a} \mathrm{cnt}_a(K_1) \cdot \mathrm{cnt}_a(K_2),
$$

where $K_1$, $K_2$ are the lists of non-null key values of the two results and $\mathrm{cnt}_a$ counts occurrences of $a$. $\mathsf{NULL}$ keys match nothing, since $\mathsf{NULL} = \mathsf{NULL}$ is $\mathsf{unknown}$. This is the multiplicity count of Guagliardo and Libkin's bag semantics: a product multiplies the multiplicities of its factors, $\mathsf{WHERE}$ keeps the tuples whose condition is true (Figure 5), and a comparison with a $\mathsf{NULL}$ argument is $\mathsf{unknown}$ (Figure 6). For $q_1 = q_2$ and $i = j$ it is the second frequency moment $F_2$ of the non-null keys.

## Proof sketch

Each pair of rows contributes one output row exactly when both keys are non-null and equal, and the pairs with common key $a$ number $\mathrm{cnt}_a(K_1)\,\mathrm{cnt}_a(K_2)$. Counting with structural equality of data instead, under which $\mathsf{NULL}$ equals $\mathsf{NULL}$, gives the same result when one input has no $\mathsf{NULL}$ key.

## Depends on

- [SQL queries with bag semantics and strict evaluation](sql-query-bag-semantics.md)

## Proof depends on

- [SQL truth values form Kleene's strong three-valued logic](sql-kleene-truth-values.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- N. Alon, Y. Matias and M. Szegedy, "The Space Complexity of Approximating the Frequency Moments", Journal of Computer and System Sciences 58(1), 1999.
