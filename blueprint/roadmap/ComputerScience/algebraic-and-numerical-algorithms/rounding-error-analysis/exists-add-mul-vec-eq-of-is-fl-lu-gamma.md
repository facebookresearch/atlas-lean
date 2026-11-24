# Backward stability of Gaussian elimination, $\gamma_{3n}$ form

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. Let $A$ be an $n \times n$ matrix over $K$ and $b \in K^n$, let $\hat L, \hat U$ be computed from $A$ by [Gaussian elimination without pivoting](is-fl-lu.md) with all pivots $\hat U_{jj}$, $j < n$, nonzero, let $\hat y$ be computed from $\hat L$ and $b$ by [forward substitution](is-fl-lower-solve.md) and $\hat x$ from $\hat U$ and $\hat y$ by [back substitution](is-fl-upper-solve.md), all in floating point. If $3nu < 1$, then there is an $n \times n$ matrix $F$ with

$$(A + F)\,\hat x = b, \qquad |F_{ij}| \le \gamma_{3n} \sum_k |\hat L_{ik}|\,|\hat U_{kj}| \quad \text{for all } i, j,$$

the form in which the bound is usually stated (N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, chapter on LU factorization).

## Informally uses

- [Backward stability of Gaussian elimination](exists-add-mul-vec-eq-of-is-fl-lu.md): the bound $(3\gamma_n + \gamma_n^2)|\hat L|\,|\hat U|$.
- [$3\gamma_n + \gamma_n^2 \le \gamma_{3n}$](three-mul-gamma-add-sq-le-gamma.md).
