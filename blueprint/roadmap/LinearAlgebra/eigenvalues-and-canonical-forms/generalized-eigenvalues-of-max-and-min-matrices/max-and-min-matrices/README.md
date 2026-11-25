# Generalized eigenvalues of a MAX matrix with respect to a MIN matrix

Let $n > 2$ and let $0 < s_1 < \dots < s_n$ be real numbers. Let $M$ and $N$ be the $n \times n$ matrices with entries $M_{ij} = \max(s_i, s_j)$ and $N_{ij} = \min(s_i, s_j)$, and put $\rho = \sqrt{s_n / s_1}$. Then, as polynomials in $X$,

$$\det(M - XN) = (-1)^n \det(N)\,(X - \rho)(X + 1)^{n-2}(X + \rho),$$

so the generalized eigenvalues of $M$ with respect to $N$ are $\rho$, $-\rho$ and $-1$, the last with multiplicity $n - 2$.

## Idea

MIN matrices $(\min(s_i, s_j))$ are covariance matrices of Brownian motion sampled at times $s_1 < \dots < s_n$, and MAX matrices are their companions. The generalized eigenvalues of the pair $(M, N)$, the roots of $\det(M - XN)$, are those of $N^{-1}M$. They turn out to depend only on the ratio of the extreme points $s_n/s_1$: every interior point contributes the eigenvalue $-1$. The source treats the analogous question for LCM and GCD matrices.

## Statements

- [Generalized eigenvalues of a MAX matrix to a MIN matrix](det-max-matrix-sub-x-smul-min-matrix.md)

## Sources

- Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki and Timo Tossavainen, "On Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices", Journal of Integer Sequences 28 (2025), Article 25.7.1.
