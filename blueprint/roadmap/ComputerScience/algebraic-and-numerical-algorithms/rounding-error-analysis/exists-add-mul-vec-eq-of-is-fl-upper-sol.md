# Backward error of floating-point back substitution

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. A vector $\hat x \in K^n$ is computed from an $n \times n$ matrix $U$ and $y \in K^n$ by back substitution in floating point when, for every $i < n$, $\hat x_i = \mathrm{fl}(\hat t^{(i)} / U_{ii})$, where $\hat t^{(i)}$ is obtained from $y_i$ by subtracting the rounded products $\mathrm{fl}(U_{ik} \hat x_k)$ for $k = n - 1, n - 2, \dots, i + 1$ in this order, rounding each subtraction (so $\hat x_{n-1} = \mathrm{fl}(y_{n-1} / U_{n-1,n-1})$). Let $U$ be an $n \times n$ upper triangular matrix with nonzero diagonal entries, let $\hat x$ be computed from $U$ and $y$ by back substitution in floating point, and let $n u < 1$. Then there is an $n \times n$ matrix $\delta U$ with

$$(U + \delta U)\,\hat x = y \quad \text{and} \quad |\delta U_{ik}| \le \gamma_n |U_{ik}| \text{ for all } i, k$$

(J. W. Demmel, Math 221 Lecture 5 notes, UC Berkeley, 2024, homework 1.11, there to first order; exact form as in N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002).

**Proof.** Back substitution is forward substitution on the system with rows and columns in reverse order, so the bound follows from the forward case by reindexing.

## Informally uses

- [Backward error of floating-point forward substitution](exists-add-mul-vec-eq-of-is-fl-lower-sol.md): applied to the reversed system.
