# Curvature is necessary for a positive definite secant update

If the [BFGS update](bfgs-update.md) $B_+$ is positive definite, $s \ne 0$, $s^\top B s \ne 0$ and
$y^\top s \ne 0$, then $y^\top s > 0$: by the [secant equation](bfgs-update-apply-self.md),
$y^\top s = s^\top B_+ s > 0$. No positive definite matrix can satisfy the secant equation when
$y^\top s \le 0$, which is why line searches must enforce the curvature condition.

## Sources

- J. E. Dennis and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear Equations*, Prentice-Hall 1983 (SIAM reprint 1996), Section 9.2 (necessity of the curvature condition for a positive definite secant update).
