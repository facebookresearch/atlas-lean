# Generalized eigenvalues of a MAX matrix to a MIN matrix

Let $n > 2$ and let
$0 < s_1 < s_2 < \dots < s_n$ be real numbers. Let $M$ be the $n \times n$ matrix with entries
$M_{ij} = \max(s_i, s_j)$, let $N$ be the $n \times n$ matrix with entries
$N_{ij} = \min(s_i, s_j)$, and put $\rho = \sqrt{s_n / s_1}$. Then, as polynomials in $X$ with
real coefficients,

$$\det(M - XN) = (-1)^n \det(N) \, (X - \rho)(X + 1)^{n-2}(X + \rho).$$

The roots of $\det(M - XN)$ are the generalized eigenvalues of $M$ to $N$.

## Sources

- Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki, and Timo Tossavainen, *On Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices*, Journal of Integer Sequences 28 (2025), Article 25.7.1, Theorem 1 (`jis-2025-25.7.1-thm-1`).
