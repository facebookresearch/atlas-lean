# Simultaneous diagonalization by congruence

Let $S$ and $P$ be real square matrices with rows
and columns indexed by a finite set $n$, where $S$ is symmetric and $P$ is positive definite. Then
there is an invertible real matrix $C$, indexed by $n$, such that $C^{\mathsf T} S C$ is diagonal
and $C^{\mathsf T} P C$ is the identity matrix.

Proof: Normalize $P$ to the identity by a congruence built from its orthonormal eigenbasis, scaled
by the inverse square roots of its eigenvalues, then orthogonally diagonalize the transformed
symmetric matrix. This is the argument of Wikipedia's "Definite matrix", section "Simultaneous
diagonalization", with the eigenbasis scaling in place of a Cholesky factor.

## Sources

- R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013), Theorem 4.5.15.
