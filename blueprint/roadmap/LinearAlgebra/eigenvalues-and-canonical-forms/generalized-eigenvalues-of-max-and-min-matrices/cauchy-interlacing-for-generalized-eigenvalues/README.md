# Cauchy interlacing for generalized eigenvalues

Let $n \ge 1$, let $A$ be a Hermitian and $B$ a positive definite complex $(n+1) \times (n+1)$ matrix,
and let $A'$ and $B'$ be their leading principal $n \times n$ submatrices. If
$\lambda_1 \ge \dots \ge \lambda_{n+1}$ are the roots of $\det(A - XB)$ and
$\lambda'_1 \ge \dots \ge \lambda'_n$ those of $\det(A' - XB')$, each counted with multiplicity, then
$\lambda_{k+1} \le \lambda'_k \le \lambda_k$ for every $k = 1, \dots, n$.

## Idea

The generalized eigenvalues of the pair $(A, B)$ are the eigenvalues of the Hermitian matrix
$B^{-1/2} A B^{-1/2}$, so they are real, and they are the critical values of the quotient
$x^* A x / x^* B x$. By the Courant–Fischer principle the $k$-th largest is the maximum, over
$k$-dimensional subspaces, of the minimum of this quotient on the subspace. The smaller pair is the
quotient restricted to the vectors whose last coordinate is $0$, and restricting to a hyperplane
moves each critical value by at most one place. For $B = I$ this is Cauchy's interlacing theorem for
Hermitian matrices.

## Statements

- [Cauchy interlacing for generalized eigenvalues](generalized-eigenvalue-interlacing.md)

## Sources

- Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki and Timo Tossavainen, "On Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices", Journal of Integer Sequences 28 (2025), Article 25.7.1.
