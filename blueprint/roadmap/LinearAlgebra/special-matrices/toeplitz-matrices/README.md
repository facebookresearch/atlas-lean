# Toeplitz matrices

A real $(n + 1) \times (n + 1)$ matrix $A = (a_{ij})$, indexed by $\{0, \dots, n\}$, is Toeplitz if there is a function $c : \mathbb{Z} \to \mathbb{R}$ with $a_{ij} = c(i - j)$ for all $i, j$: the matrix is constant along each diagonal.

## Idea

Toeplitz matrices are the matrices of truncated convolutions: multiplying by one convolves a vector with the sequence $c$. They arise as covariance matrices of stationary time series, in signal processing and in the discretization of differential and integral equations. A linear system whose matrix is symmetric, positive definite and Toeplitz can be solved in $O(n^2)$ operations by the Levinson recursion; for a general Toeplitz matrix the plain recursion breaks down when a leading principal minor vanishes, as for $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. A symmetric Toeplitz matrix comes from an even sequence, $c(-k) = c(k)$. The infinite lower-triangular Toeplitz matrix of a sequence $(a_0, a_1, \dots)$ represents multiplication by the power series $\sum_k a_k x^k$, which links Toeplitz matrices to generating functions and Riordan arrays.

## Statements

- [Toeplitz matrix](is-toeplitz-matrix.md)
- [Toeplitz matrices from coefficients](is-toeplitz-matrix-of-witness.md): a matrix with $a_{ij} = c(i - j)$ is Toeplitz
- [Symmetric Toeplitz matrix](is-symmetric-toeplitz-matrix.md): symmetric Toeplitz matrices
- [Symmetric Toeplitz matrices from even coefficients](is-symmetric-toeplitz-matrix-of-witness.md): they come from even sequences
- [Symmetric Toeplitz matrices are Toeplitz](is-toeplitz.md): they are Toeplitz
- [Symmetric Toeplitz matrices are symmetric](entry-comm.md): they are symmetric
- [Lower-triangular Toeplitz matrix](lower-toeplitz.md): the infinite lower-triangular Toeplitz matrix of a sequence
- [Entries on and below the diagonal of a lower-triangular Toeplitz matrix](lower-toeplitz-apply-of-le.md): its entries on and below the diagonal
- [Entries above the diagonal of a lower-triangular Toeplitz matrix](lower-toeplitz-apply-of-gt.md): its entries above the diagonal
- [Diagonal entries of a lower-triangular Toeplitz matrix](lower-toeplitz-apply-diag.md): its diagonal entries
