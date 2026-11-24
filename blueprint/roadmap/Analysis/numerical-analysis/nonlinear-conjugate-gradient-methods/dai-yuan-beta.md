# Dai–Yuan conjugate gradient parameter

For the gradient $g$ at the current point, the gradient $g'$ at the next point and the current
search direction $d$, the Dai–Yuan parameter is

$$\beta^{DY} = \frac{\|g'\|^2}{d^\top (g' - g)} .$$

It has the numerator of the Fletcher–Reeves formula $\|g'\|^2 / \|g\|^2$ and the denominator of the
Hestenes–Stiefel formula $g'^\top (g' - g) / d^\top (g' - g)$, and it coincides with the
Fletcher–Reeves formula when the line searches are exact. When $d$ is a descent direction and the
Wolfe curvature condition holds with $\sigma < 1$, $d^\top (g' - g) > 0$, so the parameter is well
defined and positive.

## Background

- [One Hestenes–Stiefel conjugate gradient step](../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/step.md): the linear conjugate gradient
  method for $Ax = b$ that the nonlinear methods reduce to on strictly convex quadratics with exact
  line searches.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, formula (2.4).
