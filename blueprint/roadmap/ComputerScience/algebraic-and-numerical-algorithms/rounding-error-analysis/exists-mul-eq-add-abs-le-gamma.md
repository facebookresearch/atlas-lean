# Backward error of floating-point LU factorization

Let $K$ be a linearly ordered field with a floor function (for instance $\mathbb{Q}$ or $\mathbb{R}$) and $p$ a natural number. Write $\mathrm{fl}$ for rounding to nearest, ties to even, to binary floating-point numbers with $p$-bit significands and unbounded exponent, $u = 2^{-p}$ for the unit roundoff and $\gamma_k = k u / (1 - k u)$. Let $\hat L$ and $\hat U$ be the [factors computed by Gaussian elimination without pivoting](is-fl-lu.md) in floating point from an $n \times n$ matrix $A$ over $K$, with nonzero pivots $\hat U_{jj}$ for $j < n - 1$ (the last pivot is never divided by), and let $n u < 1$. Then there is an $n \times n$ matrix $E$ with

$$\hat L \hat U = A + E, \qquad |E_{ij}| \le \gamma_n \sum_k |\hat L_{ik}|\,|\hat U_{kj}| \quad \text{for all } i, j.$$

J. W. Demmel's Math 221 course (UC Berkeley, Lecture 5 notes, 2024) states this as "$A - E = P L U$ where $|E| \le n\,\varepsilon\, P |L|\,|U|$", to first order in $\varepsilon = u$ and with $P = I$ in the proof; the exact $\gamma_n$ form is the one of N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002, in the chapter on LU factorization. Gaussian elimination is therefore backward stable as long as $\|\,|\hat L|\,|\hat U|\,\|$ is a modest multiple of $\|A\|$; the ratio is the pivot growth factor, which partial pivoting keeps small in practice although it can reach $2^{n-1}$. Adding the backward errors of the two triangular solves gives [$(A + F)\hat x = b$ with $|F| \le (3\gamma_n + \gamma_n^2)\,|\hat L|\,|\hat U|$](exists-add-mul-vec-eq-of-is-fl-lu.md) for the computed solution of $Ax = b$, and then the [condition number bound](../../../LinearAlgebra/matrix-decompositions/perturbation-theory-for-linear-systems/norm-sub-div-norm-le.md) bounds its error.

**Proof.** For an entry of $\hat U$ ($i \le j$), $E_{ij} = \hat U_{ij} + \sum_{k<i} \hat L_{ik}\hat U_{kj} - A_{ij}$, and the [error of the floating-point $c - \sum a_k b_k$, measured by the result](abs-sub-dot-fl-add-sum-sub-le.md), bounds it by $\gamma_i(\sum_{k<i} |\hat L_{ik}\hat U_{kj}| + |\hat U_{ij}|)$. For an entry of $\hat L$ ($i > j$) the division by the pivot adds one rounding, of relative size $\gamma_1$ [measured by the rounded value](abs-fl-sub-le-gamma-one-mul.md), and [$(1 + \gamma_j)(1 + \gamma_1) \le 1 + \gamma_{j+1}$](one-add-gamma-mul-le.md) absorbs it. Both indices are below $n$, and [$\gamma$ is monotone](gamma-mono.md).

## Informally uses

- [Error of a floating-point $c - \sum a_k b_k$, measured by the result](abs-sub-dot-fl-add-sum-sub-le.md): applied to each Doolittle formula.
- [Composition of relative errors](one-add-gamma-mul-le.md): absorbs the rounding of the division by the pivot.

## Background

- [Forward error of the floating-point dot product](abs-dot-fl-sub-le.md): the same error accounting for a plain inner product, measured against the exact terms rather than the computed result.
- [No element growth in Cholesky factorization](sum-abs-mul-abs-le-sqrt-mul-sqrt.md): for symmetric positive definite matrices the factor $|L|\,|L^T|$ is bounded without pivoting.
