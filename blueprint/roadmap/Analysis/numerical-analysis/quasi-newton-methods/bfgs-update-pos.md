# The BFGS update preserves positive definiteness under the curvature condition

If $B$ is symmetric and positive definite, $s \ne 0$ and the curvature condition $y^\top s > 0$
holds, then the [BFGS update](bfgs-update.md) $B_+$ is positive definite.

Proof: with $t = (Bs)^\top v / s^\top B s$ and $u = v - t s$,

$$v^\top B_+ v = u^\top B u + \frac{(y^\top v)^2}{y^\top s} .$$

Both terms are nonnegative; the first vanishes only if $v = t s$, and then the second is
$t^2\, y^\top s > 0$ unless $v = 0$. Conversely, $y^\top s > 0$ is
[necessary](inner-pos-of-bfgs-update-pos.md), so the BFGS update preserves positive definiteness
exactly when the curvature condition holds.

## Background

- [Standard Wolfe conditions](../line-search-methods/wolfe-conditions.md): a Wolfe step along a
  descent direction always gives $y^\top s > 0$.

## Sources

- J. E. Dennis and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear Equations*, Prentice-Hall 1983 (SIAM reprint 1996), Section 9.2.
