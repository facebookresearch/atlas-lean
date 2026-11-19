# Rounding error analysis

Rounding error analysis bounds the error of an algorithm run in floating point, from the model $\mathrm{fl}(a \mathbin{\mathrm{op}} b) = (a \mathbin{\mathrm{op}} b)(1 + \delta)$, $|\delta| \le u$, of [floating-point rounding](../floating-point-rounding/README.md). Its central notion is backward stability: an algorithm is backward stable if its computed result is the exact result for slightly perturbed data. The error of a backward stable algorithm is then at most its backward error times the [condition number](../../../LinearAlgebra/matrix-decompositions/perturbation-theory-for-linear-systems/README.md) of the problem.

A sum of $n$ rounded products is accurate to $\gamma_n = nu/(1 - nu)$ relative to $\sum_i |x_i y_i|$, so a floating-point matrix product satisfies $|\mathrm{fl}(AB) - AB| \le \gamma_n |A|\,|B|$ entrywise. The same analysis applied to the Doolittle formulas shows that Gaussian elimination computes the exact LU factors of $A + E$ with $|E| \le \gamma_n |\hat L|\,|\hat U|$: with the two triangular solves, the computed solution of $Ax = b$ solves $(A + F)\hat x = b$ with $|F| \le (3\gamma_n + \gamma_n^2)|\hat L|\,|\hat U|$, so Gaussian elimination is backward stable when $|\hat L|\,|\hat U|$ is not much larger than $A$, which partial pivoting achieves in practice. For Cholesky factorization $|L|\,|L^T|$ is always bounded by the largest diagonal entry of $A$, so no pivoting is needed. The statements follow J. W. Demmel's Math 221 notes, which give the bounds to first order in the machine precision; the exact $\gamma_n$ forms are those of N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002.
- [Forward error of the floating-point dot product](abs-dot-fl-sub-le.md)
- [Forward error of floating-point matrix multiplication](abs-mat-mul-fl-sub-le.md)
- [Floating-point dot product](dot-fl.md)
- [The constant $\gamma_n$ of rounding error analysis](gamma.md)
- [$\gamma_k$ is nonnegative](gamma-nonneg.md)
- [Growth of $\gamma$ by one rounding](gamma-step.md)
- [One rounding stays within $\gamma_1$](le-gamma-one.md)
- [Floating-point matrix product](mat-mul-fl.md)
- [Two roundings stay within $\gamma_{k+1}$](two-mul-add-sq-le-gamma.md)
- [Factors computed by floating-point Gaussian elimination without pivoting](is-fl-lu.md)
- [Column of a matrix as a sequence](col-seq.md)
- [Floating-point LU of a $1 \times 1$ matrix](is-fl-lu-one-by-one.md)
- [Row of a matrix as a sequence](row-seq.md)
- [Floating-point evaluation of $c - \sum_{k<m} a_k b_k$](sub-dot-fl.md)
- [Backward error of floating-point LU factorization](exists-mul-eq-add-abs-le-gamma.md)
- [No element growth, max form](sum-abs-mul-abs-le-of-diag-le.md)
- [No element growth in Cholesky factorization](sum-abs-mul-abs-le-sqrt-mul-sqrt.md)
- [Rounding error relative to the rounded value](abs-fl-sub-le-gamma-one-mul.md)
- [Error of a floating-point $c - \sum_k a_k b_k$, measured by the result](abs-sub-dot-fl-add-sum-sub-le.md)
- [Monotonicity of $\gamma$](gamma-mono.md)
- [Composition of relative errors](one-add-gamma-mul-le.md)
- [Forward substitution in floating point](is-fl-lower-solve.md)
- [Back substitution in floating point](is-fl-upper-solve.md)
- [Residual bound for one division step](abs-sub-sum-sub-mul-le.md)
- [Backward stability of Gaussian elimination](exists-add-mul-vec-eq-of-is-fl-lu.md)
- [Backward error of floating-point forward substitution](exists-add-mul-vec-eq-of-is-fl-lower-sol.md)
- [Backward error of floating-point back substitution](exists-add-mul-vec-eq-of-is-fl-upper-sol.md)
- [Residuals as componentwise perturbations](exists-perturbation-of-abs-le.md)
- [Vector as a sequence](vec-seq.md)
- [Splitting a sum at its last nonzero term](sum-fin-eq-sum-range-add.md)
- [Backward stability of Gaussian elimination, $\gamma_{3n}$ form](exists-add-mul-vec-eq-of-is-fl-lu-gamma.md)
- [$3\gamma_n + \gamma_n^2 \le \gamma_{3n}$](three-mul-gamma-add-sq-le-gamma.md)

## Related topics

- [Floating-point rounding](../floating-point-rounding/README.md): the rounding model.
- [Perturbation theory for linear systems](../../../LinearAlgebra/matrix-decompositions/perturbation-theory-for-linear-systems/README.md): condition numbers, which turn backward errors into forward errors.
- [LU decomposition](../../../LinearAlgebra/matrix-decompositions/lu-decomposition/README.md): the exact factorization.
