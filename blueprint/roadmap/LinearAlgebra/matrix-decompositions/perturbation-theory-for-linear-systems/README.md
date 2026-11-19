# Perturbation theory for linear systems

How much can the solution of $Ax = b$ change when $A$ and $b$ change? The answer is governed by the condition number $\kappa(A) = \|A\|\,\|A^{-1}\|$: if $\|E\|\,\|A^{-1}\| < 1$, then $A - E$ is invertible, and the solution $x + \delta x$ of $(A - E)(x + \delta x) = b + f$ satisfies

$$\frac{\|\delta x\|}{\|x\|} \le \frac{\kappa(A)}{1 - \|E\|\,\|A^{-1}\|} \left(\frac{\|f\|}{\|b\|} + \frac{\|E\|}{\|A\|}\right).$$

Together with backward stability (the computed solution exactly solves a system whose data differ from $A$ and $b$ by a few units of roundoff relative to their size), this bounds the error of a computed solution by about $\kappa(A)$ times the machine precision. In the 2-norm, $1/\kappa(A)$ is exactly the relative distance from $A$ to the nearest singular matrix, and the backward error of an approximate solution $\hat x$ is its residual $\|A\hat x - b\|$ divided by $\|\hat x\|$.

The statements follow J. W. Demmel's graduate course (Math 221, UC Berkeley, Lecture 3 notes of 10 September 2024; course text J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997). They hold for bounded operators on Banach and Hilbert spaces, which include square matrices with an operator norm.
- [Backward error of an approximate solution](is-least-norm-backward-error.md)
- [Distance to the nearest singular operator](is-least-norm-of-not-is-unit-sub.md)
- [Small perturbations of an invertible element stay invertible](is-unit-sub.md)
- [Norm of the inverse under perturbation](norm-inverse-sub-le.md)
- [Change of the inverse](norm-inverse-sub-sub-le.md)
- [Condition number bound for linear systems](norm-sub-div-norm-le.md)
- [Condition number bound, right-hand side perturbed only](norm-sub-div-norm-le-of-rhs.md)
- [The condition number is at least one](one-le-norm-mul-norm-inv.md)

## Related topics

- [Rounding error analysis](../../../ComputerScience/algebraic-and-numerical-algorithms/rounding-error-analysis/README.md): backward error bounds for floating-point dot products, matrix products and LU factorization, which this theory turns into forward error bounds.
- [Bauer–Fike theorem](../../../Analysis/operator-theory/eigenvalue-inequalities/bauer-fike-theorem/README.md): perturbation theory for eigenvalues.
- [Singular value decomposition](../singular-value-decomposition/README.md): in the 2-norm $\kappa_2(A) = \sigma_{\max}/\sigma_{\min}$.
