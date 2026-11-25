# The matrix exponential is a standard matrix function

For a Hermitian matrix $A$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$ and a real number $\theta$, the power-series matrix exponential satisfies

$$e^{\theta A} = \sum_{q \ge 0} \frac{(\theta A)^q}{q!} = f_\theta(A), \qquad f_\theta(a) = e^{\theta a},$$

where $f_\theta(A)$ is the standard matrix function given by the continuous functional calculus. The proof diagonalizes $\theta A = U\,\operatorname{diag}(\theta\lambda_i)\,U^{*}$ with a unitary $U$, and uses that the exponential commutes with conjugation by $U$ and acts entrywise on a diagonal matrix. In a C⋆-algebra the same identity holds for every self-adjoint element; for matrices the diagonalization argument proves it directly, without choosing a norm.

## Background

- [Determinant of the matrix exponential](../../../determinants-and-matrix-identities/matrix-exponential/matrix-det-exp-eq-exp-trace.md): background, the companion identity $\det e^A = e^{\operatorname{tr} A}$ for the same power-series exponential.

## Sources

- J. A. Tropp, An Introduction to Matrix Concentration Inequalities, Found. Trends Mach. Learn. 8 (2015), 1–230, arXiv:1501.01571, §2.1.11, display (2.1.15).
