# Existence of the reduced QR factorization

Let $A$ be a real $m \times k$ matrix whose columns are linearly independent (full column
rank, so $k \le m$). Then there are an $m \times k$ matrix $Q$ with orthonormal columns,
$Q^{\mathsf{T}} Q = I_k$, and an upper triangular $k \times k$ matrix $R$ with positive diagonal
entries such that $A = QR$.

Proof: Gram–Schmidt orthonormalization of the columns of $A$.

## Background

- [Real singular value decomposition](../singular-value-decomposition/real-singular-value-decomposition.md): the other orthogonal factorization of a rectangular matrix; QR is computable in finitely many steps, the SVD is not.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 7 (the QR factorization; full-rank case, with $r_{jj} > 0$).
- G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins (2013), Section 5.2.
