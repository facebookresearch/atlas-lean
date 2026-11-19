# The BFGS update satisfies the secant equation

If $s^\top B s \ne 0$ and $y^\top s \ne 0$, the [BFGS update](bfgs-update.md) satisfies the secant
equation

$$B_+ s = y ,$$

the defining property of quasi-Newton updates: along the last step, $B_+$ reproduces the change of
the gradient, as the true Hessian does for a quadratic.

## Sources

- J. E. Dennis and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear Equations*, Prentice-Hall 1983 (SIAM reprint 1996), Section 9.2 (the BFGS update "obeys $H_+ s_c = y_c$").
