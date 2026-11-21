# BFGS update

For a Hessian approximation $B$, a step $s = x_+ - x$ and a gradient change
$y = \nabla f(x_+) - \nabla f(x)$, the BFGS update (Broyden, Fletcher, Goldfarb and Shanno, 1970) is

$$B_+ = B - \frac{(Bs)(Bs)^\top}{s^\top B s} + \frac{y\, y^\top}{y^\top s},$$

that is $B_+ v = Bv - \frac{(Bs)^\top v}{s^\top B s}\, Bs + \frac{y^\top v}{y^\top s}\, y$. It is a
symmetric correction of rank at most two that satisfies the
[secant equation](bfgs-update-apply-self.md) $B_+ s = y$ and keeps $B$
[positive definite](bfgs-update-pos.md) when $y^\top s > 0$.

## Sources

- J. E. Dennis and R. B. Schnabel, *Numerical Methods for Unconstrained Optimization and Nonlinear Equations*, Prentice-Hall 1983 (SIAM reprint 1996), Section 9.2.
