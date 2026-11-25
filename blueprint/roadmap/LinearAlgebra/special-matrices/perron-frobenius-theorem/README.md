# Perron–Frobenius theorem

Let $A$ be a real square matrix indexed by a nonempty finite set, and suppose $A$ is irreducible: its entries are nonnegative, and for all indices $i, j$ there is a path $i = i_0, i_1, \dots, i_k = j$ of length $k \ge 1$ with $A_{i_{t-1} i_t} > 0$ for every $t$. Then there are a real number $r > 0$ and a vector $v$ with positive entries such that $Av = rv$, and every complex eigenvalue $\mu$ of $A$ satisfies $|\mu| \le r$.

## Idea

A nonnegative matrix whose directed graph is strongly connected has a dominant eigenvalue, the spectral radius, with an eigenvector of positive entries. This is the mathematics behind the stationary distribution of a Markov chain, the PageRank vector, the stable age distribution in Leslie population models and the growth rate in Leontief economics. Paths have positive length here, so a $1 \times 1$ zero matrix is not irreducible. A standard proof maximizes the Collatz–Wielandt function $\min_i (Av)_i / v_i$ over vectors $v$ with positive entries. The full theorem also says that $r$ is a simple eigenvalue, that its eigenvectors with positive entries form a single ray, and that no other eigenvalue has a nonzero eigenvector with nonnegative entries; for primitive matrices every other eigenvalue is strictly smaller in modulus.

## Statements

- [Perron–Frobenius theorem for irreducible nonnegative matrices](perron-frobenius.md)
- [Perron–Frobenius theorem for nonzero irreducible nonnegative matrices](perron-frobenius-2.md): a variant for nonzero irreducible matrices
- [Complexification of a real matrix](to-complex-matrix.md): the complexification of a real matrix, used to speak of its complex eigenvalues
- [Perron–Frobenius theorem for primitive nonnegative matrices](perron-frobenius-for-primitive-nonnegative-matri.md): simplicity, strict dominance and convergence of normalized powers
- [Positive left Perron vector of an irreducible matrix](positive-left-perron-vector.md)
