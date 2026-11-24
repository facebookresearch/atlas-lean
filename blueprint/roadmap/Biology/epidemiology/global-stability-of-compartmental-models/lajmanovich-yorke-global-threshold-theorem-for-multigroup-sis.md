# Lajmanovich–Yorke threshold theorem for multigroup SIS

In the Lajmanovich–Yorke SIS model with $d$ groups, $x_i \in [0, 1]$ is the proportion of infected individuals in group $i$ and

$$\dot x_i = (1 - x_i)\sum_j C_{ij} x_j - D_i x_i,$$

with infection rates $C_{ij} \ge 0$ and cure rates $D_i > 0$. Suppose $C$ is irreducible, let $A = C - \mathrm{diag}(D_i)$ and let $\lambda(A)$ be the largest real part of the eigenvalues of $A$. The theorem of Lajmanovich and Yorke (1976), as stated by Benaïm in lecture slides on the model, says: if $\lambda(A) \le 0$, the disease-free equilibrium $0$ is a global attractor; if $\lambda(A) > 0$, there is another equilibrium $x^* \gg 0$ and every nonzero trajectory converges to $x^*$, which is therefore the unique equilibrium with positive coordinates.

## Expansion

1. The model: forward invariance of $[0, 1]^d$, and $A$ as the Jacobian at $0$, an irreducible Metzler matrix.
2. The case $\lambda(A) \le 0$: a linear Lyapunov function built from a positive left eigenvector of $A$.
3. The case $\lambda(A) > 0$: existence of $x^* \gg 0$ and global convergence (the system is cooperative and its vector field is strictly sublinear).
4. The equivalence of $\lambda(A) \le 0$ with $\rho(\mathrm{diag}(D_i)^{-1}C) \le 1$, via [nonsingular M-matrices](../../../LinearAlgebra/special-matrices/m-matrices-and-hurwitz-stability/nonsingular-m-matrices/is-nonsingular-mmatrix.md), so that the threshold is a reproduction number; and the random-environment version in the slides, as a separate statement.

## Sources

- M. Benaïm, Lajmanovich and Yorke SIS model, lecture slides (based on joint work with E. Strickler), Aussois summer school, 2017, slide stating the theorem of Lajmanovich and Yorke.
- Original result: A. Lajmanovich and J. A. Yorke, A deterministic model for gonorrhea in a nonhomogeneous population, Math. Biosci. 28 (1976), 221–236. <https://doi.org/10.1016/0025-5564(76)90125-5> The threshold statement follows Benaïm's slides.
