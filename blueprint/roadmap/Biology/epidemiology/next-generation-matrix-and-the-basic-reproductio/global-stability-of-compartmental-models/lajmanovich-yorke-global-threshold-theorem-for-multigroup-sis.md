# Lajmanovich–Yorke threshold theorem for multigroup SIS

In the Lajmanovich–Yorke SIS model with $d$ groups, $x_i \in [0, 1]$ is the proportion of infected individuals in group $i$ and

$$\dot x_i = (1 - x_i)\sum_j C_{ij} x_j - D_i x_i,$$

with infection rates $C_{ij} \ge 0$ and cure rates $D_i > 0$. Suppose $C$ is irreducible, let $A = C - \mathrm{diag}(D_i)$ and let $\lambda(A)$ be the largest real part of the eigenvalues of $A$. The theorem of Lajmanovich and Yorke (1976), as restated by Benaïm and Strickler (2019, Theorem 4.1), says: if $\lambda(A) \le 0$, the disease-free equilibrium $0$ is a global attractor; if $\lambda(A) > 0$, there is another equilibrium $x^* \gg 0$ and every nonzero trajectory converges to $x^*$, which is therefore the unique equilibrium with positive coordinates.

## Proof depends on

- [Nonsingular M-matrix](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md)

## Expansion

1. The model: forward invariance of $[0, 1]^d$, and $A$ as the Jacobian at $0$, an irreducible Metzler matrix.
2. The case $\lambda(A) \le 0$: a linear Lyapunov function built from a positive left eigenvector of $A$.
3. The case $\lambda(A) > 0$: existence of $x^* \gg 0$ and global convergence (the system is cooperative and its vector field is strictly sublinear).
4. The equivalence of $\lambda(A) \le 0$ with $\rho(\mathrm{diag}(D_i)^{-1}C) \le 1$, via [nonsingular M-matrices](../../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md), so that the threshold is a reproduction number; and the random-environment version of Benaïm and Strickler (2019, Section 4), as a separate statement.

## Sources

- Original result: A. Lajmanovich and J. A. Yorke, A deterministic model for gonorrhea in a nonhomogeneous population, Math. Biosci. 28 (1976), 221–236. <https://doi.org/10.1016/0025-5564(76)90125-5>
- M. Benaïm and E. Strickler, Random switching between vector fields having a common zero, Ann. Appl. Probab. 29 (2019), 326–375, Section 4, Theorem 4.1. <https://doi.org/10.1214/18-AAP1418>
