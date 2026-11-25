# Polar decomposition of invertible complex matrices

Let $A$ be a complex square matrix with
rows and columns indexed by a finite set, and suppose $\det A \ne 0$. Then there are a unitary
matrix $U$ and a positive-definite Hermitian matrix $P$ with $A = UP$, and they are unique: if
$U'$ is unitary, $P'$ is positive-definite Hermitian and $A = U'P'$, then $U' = U$ and $P' = P$.

Proof: take $P$ to be the positive-definite square root of $A^* A$ and $U = AP^{-1}$, the
construction in Wikipedia, "Polar decomposition".

## Sources

- R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 7.3.1.
