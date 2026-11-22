# The Arnoldi relation

Let $T$ be a linear operator on a real or complex inner product space, $r$ a vector, $q_0, \dots, q_{k-1}$
the Arnoldi vectors and $h_{ij} = \langle q_i, T q_j \rangle$. If the Krylov vectors
$r, Tr, \dots, T^{k-1} r$ are linearly independent and $j + 1 < k$, then
$T q_j = \sum_{i=0}^{k-1} h_{ij}\, q_i$.
Only the terms with $i \le j + 1$ are nonzero ([upper Hessenberg form](hessenberg-eq-zero.md)). With
$n = k - 1$, $Q_n = [q_0, \dots, q_{n-1}]$ and $\tilde H_n = (h_{ij})_{i \le n,\, j < n}$, these relations
for $j < n$ are the columns of $T Q_n = Q_{n+1} \tilde H_n$.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 33.
