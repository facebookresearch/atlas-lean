# Condition number bound for linear systems

Let $A$ be an invertible bounded operator on a Banach space, for instance a nonsingular square matrix with an operator norm, with $Ax = b \ne 0$. Let $(A - E)(x + \delta x) = b + f$ with $\|E\|\,\|A^{-1}\| < 1$. Then

$$\frac{\|\delta x\|}{\|x\|} \le \frac{\|A\|\,\|A^{-1}\|}{1 - \|E\|\,\|A^{-1}\|} \left(\frac{\|f\|}{\|b\|} + \frac{\|E\|}{\|A\|}\right).$$

## Idea

How much can the solution of $Ax = b$ change when the data change? The answer is governed by the condition number $\kappa(A) = \|A\|\,\|A^{-1}\|$: the relative error in $x$ is at most about $\kappa(A)$ times the relative changes in $A$ and $b$. The hypothesis $\|E\|\,\|A^{-1}\| < 1$ keeps $A - E$ invertible, by a Neumann series. Combined with backward stability, it shows that a good algorithm computes $x$ to a relative accuracy of about $\kappa(A)$ times the machine precision. The condition number is at least $1$, and in the 2-norm $1/\kappa(A)$ is exactly the relative distance from $A$ to the nearest singular matrix.

## Statements

- [Condition number bound for linear systems](norm-sub-div-norm-le.md)
- [Condition number bound, right-hand side perturbed only](norm-sub-div-norm-le-of-rhs.md): special case: only the right-hand side is perturbed
- [Small perturbations of an invertible element stay invertible](is-unit-sub.md): small perturbations of an invertible element stay invertible
- [Norm of the inverse under perturbation](norm-inverse-sub-le.md): a bound on the norm of the perturbed inverse
- [Change of the inverse](norm-inverse-sub-sub-le.md): the change of the inverse
- [The condition number is at least one](one-le-norm-mul-norm-inv.md): the condition number is at least $1$
- [Distance to the nearest singular operator](is-least-norm-of-not-is-unit-sub.md): the meaning of the condition number in the statement: in the 2-norm, on a nonzero finite-dimensional inner product space, $1/\kappa(A)$ is the relative distance from $A$ to the singular operators

## Related topics

- [Rounding error analysis](../../../../ComputerScience/algebraic-and-numerical-algorithms/rounding-error-analysis/README.md): backward error bounds for floating-point dot products, matrix products and LU factorization, which this theory turns into forward error bounds.
- [Bauer–Fike theorem](../../../../Analysis/operator-theory/eigenvalue-inequalities/bauer-fike-theorem/README.md): perturbation theory for eigenvalues.
- [Singular value decomposition of a complex matrix](../../singular-value-decomposition/singular-value-decomposition-theorem/complex-singular-value-decomposition.md): in the 2-norm $\kappa_2(A) = \sigma_{\max}/\sigma_{\min}$.
