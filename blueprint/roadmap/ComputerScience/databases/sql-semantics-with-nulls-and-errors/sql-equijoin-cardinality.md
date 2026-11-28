# Equijoin cardinality equals the join size of non-null keys

For queries $q_1, q_2$ and key columns $i$ of $q_1$ and $j$ of $q_2$ of a common type $\tau$, on a conforming instance on which both succeed, the number of rows of $q_1\ \mathsf{JOIN}\ q_2\ \mathsf{ON}\ q_1.i = q_2.j$ equals

$$
\sum_{a} \mathrm{cnt}_a(K_1) \cdot \mathrm{cnt}_a(K_2),
$$

where $K_1$, $K_2$ are the lists of non-null key values of the two results and $\mathrm{cnt}_a$ counts occurrences of $a$. This is the join size $|R_1 \bowtie R_2| = \sum_{i \in D} f_i\, g_i$ of Alon, Gibbons, Matias and Szegedy (Section 1), with $f_a = \mathrm{cnt}_a(K_1)$ and $g_a = \mathrm{cnt}_a(K_2)$ the frequencies of the key value $a$ in the two results. $\mathsf{NULL}$ keys match nothing: in Guagliardo and Libkin's semantics a comparison with a $\mathsf{NULL}$ argument, $\mathsf{NULL} = \mathsf{NULL}$ included, is $\mathsf{unknown}$ (Figure 6), and $\mathsf{WHERE}$ keeps only the tuples whose condition is true (Figure 5). For $q_1 = q_2$ and $i = j$ it is the self-join size, the second frequency moment $F_2$ of the non-null keys (Alon, Gibbons, Matias and Szegedy, Section 1).

## Proof sketch

In Guagliardo and Libkin's bag semantics a product multiplies the multiplicities of its factors (Section 3), so each pair of rows contributes one output row exactly when both keys are non-null and equal, and the pairs with common key $a$ number $\mathrm{cnt}_a(K_1)\,\mathrm{cnt}_a(K_2)$. Counting with structural equality of data instead, under which $\mathsf{NULL}$ equals $\mathsf{NULL}$, gives the same result when one input has no $\mathsf{NULL}$ key.

## Depends on

- [SQL queries with bag semantics and strict evaluation](sql-query-bag-semantics.md)

## Proof depends on

- [SQL truth values form Kleene's strong three-valued logic](sql-kleene-truth-values.md)

## Sources

- P. Guagliardo and L. Libkin, "A Formal Semantics of SQL Queries, Its Validation, and Applications", Proceedings of the VLDB Endowment 11(1), 2017.
- N. Alon, Y. Matias and M. Szegedy, "The Space Complexity of Approximating the Frequency Moments", Journal of Computer and System Sciences 58(1), 1999.
- N. Alon, P. B. Gibbons, Y. Matias and M. Szegedy, "Tracking Join and Self-Join Sizes in Limited Storage", Journal of Computer and System Sciences 64(3), 2002, Section 1; authors' copy: <http://theory.stanford.edu/~matias/papers/tracking_jcss.pdf>.
