# Uniqueness of the reduced QR factorization

Let $Q, Q'$ be real $m \times k$ matrices with $Q^{\mathsf{T}} Q = Q'^{\mathsf{T}} Q' = I_k$
and let $R, R'$ be upper triangular $k \times k$ matrices with positive diagonal entries. If
$QR = Q'R'$, then $Q = Q'$ and $R = R'$.

Proof: $U = R' R^{-1}$ is upper triangular with positive diagonal and satisfies
$U^{\mathsf{T}} U = I$, so $U^{\mathsf{T}} = U^{-1}$ is both upper and lower triangular, hence
diagonal with entries $1$. The sign condition is needed: $(-I)(-I) = I \cdot I$.

## Sources

- L. N. Trefethen and D. Bau III, Numerical Linear Algebra, SIAM (1997), Lecture 7 (the QR factorization).
