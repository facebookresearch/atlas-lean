# Exact LDL certificates for positive definiteness

A symmetric rational matrix $M$ is positive definite if and only if $M = L\, \mathrm{diag}(d)\, L^\top$ for a unit lower-triangular rational $L$ and a rational vector $d$ with all $d_i > 0$, and positive semidefinite if such a factorization exists with all $d_i \ge 0$ (allowing the factorization to exist only after symmetric permutation when pivots vanish). Hence a proposed $(L, d)$ can be checked exactly by rational matrix multiplication, which certifies positive (semi)definiteness, and with a quadratic Lyapunov certificate $P \succ 0$, $A^\top P + PA \prec 0$, it certifies exponential stability of $\dot x = Ax$.

## Proof sketch

$x^\top M x = \sum_i d_i (L^\top x)_i^2$ and $L^\top$ is invertible; conversely symmetric Gaussian elimination without pivoting on a positive definite matrix produces positive pivots.

## Depends on

- [Existence of the reduced row echelon form](../../../LinearAlgebra/matrix-decompositions/gaussian-elimination-and-row-echelon-form/exists-is-reduced-row-echelon-row-equiva.md)

## Sources

- A. Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
