# Weyl's inequality for singular values

For linear maps $T, U : E \to F$ between finite-dimensional inner product spaces and every
$k \ge 0$, $|\sigma_k(T) - \sigma_k(U)| \le \|T - U\|_2$, where $\sigma_0 \ge \sigma_1 \ge \cdots$ are the
singular values, indexed from $0$ and followed by zeros, and $\|\cdot\|_2$ is the spectral norm.
Singular values are perfectly conditioned:
a perturbation of norm $\varepsilon$ moves each of them by at most $\varepsilon$, for every
matrix, normal or not.

## Background

- [Condition numbers of sign matrices](../../condition-numbers-of-sign-matrices/README.md): condition numbers as ratios of extreme singular values.

## Sources

- G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins (2013), Section 8.6.1.
- R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge (2013), Section 7.3.
- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 12 (conditioning).
