# Backward stability of Gaussian elimination

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. Let $A$ be an $n \times n$ matrix over $K$ and $b \in K^n$. Solve $Ax = b$ in floating point by computing $\hat L, \hat U$ by [Gaussian elimination without pivoting](is-fl-lu.md), with all pivots $\hat U_{jj}$, $j < n$, nonzero, then $\hat y$ from $\hat L$ and $b$ by [forward substitution](is-fl-lower-solve.md) and $\hat x$ from $\hat U$ and $\hat y$ by [back substitution](is-fl-upper-solve.md). If $n u < 1$, then there is an $n \times n$ matrix $F$ with

$$(A + F)\,\hat x = b, \qquad |F_{ij}| \le (3\gamma_n + \gamma_n^2) \sum_k |\hat L_{ik}|\,|\hat U_{kj}| \quad \text{for all } i, j.$$

This is the corollary "$(A - F)\hat x = b$ where $|F| \le 3 n\,\varepsilon\, P|L|\,|U|$" of J. W. Demmel's Math 221 course (UC Berkeley, Lecture 5 notes, 2024), there to first order in $\varepsilon = u$ and with $P = I$. The usual statement of this bound has $\gamma_{3n}|\hat L|\,|\hat U|$ (N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter on LU factorization); since [$3\gamma_n + \gamma_n^2 \le \gamma_{3n}$](three-mul-gamma-add-sq-le-gamma.md) when $3nu < 1$, the form here is slightly stronger, and it needs only $nu < 1$; it implies the [$\gamma_{3n}$ form](exists-add-mul-vec-eq-of-is-fl-lu-gamma.md). With the [condition number bound](../../../LinearAlgebra/matrix-decompositions/perturbation-theory-for-linear-systems/condition-number-bound/norm-sub-div-norm-le.md) it gives the error bound $\|\hat x - x\|/\|x\| \lesssim \kappa(A) \cdot 3 n u \cdot \|\,|\hat L|\,|\hat U|\,\|/\|A\|$, the last factor being the pivot growth.

**Proof.** $\hat L \hat U = A + E$ with $|E| \le \gamma_n |\hat L|\,|\hat U|$; $(\hat L + \delta L)\hat y = b$ with $|\delta L| \le \gamma_n |\hat L|$; $(\hat U + \delta U)\hat x = \hat y$ with $|\delta U| \le \gamma_n |\hat U|$. Then $b = (\hat L + \delta L)(\hat U + \delta U)\hat x = (A + F)\hat x$ with $F = E + \delta L\,\hat U + \hat L\,\delta U + \delta L\,\delta U$.

## Informally uses

- [Backward error of floating-point LU factorization](exists-mul-eq-add-abs-le-gamma.md): the bound on $E$.
- [Backward error of floating-point forward substitution](exists-add-mul-vec-eq-of-is-fl-lower-sol.md): the bound on $\delta L$.
- [Backward error of floating-point back substitution](exists-add-mul-vec-eq-of-is-fl-upper-sol.md): the bound on $\delta U$.
