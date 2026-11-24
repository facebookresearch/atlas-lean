# Descent of the Dai–Yuan direction

Let $d$ be a descent direction at a point with gradient $g$ ($g^\top d < 0$), and let the gradient
$g' \ne 0$ at the next point satisfy the Wolfe curvature condition $g'^\top d \ge \sigma\, g^\top d$
with $\sigma < 1$. Then $d^\top (g' - g) \ge (\sigma - 1)\, g^\top d > 0$, and the Dai–Yuan direction
$d' = -g' + \beta^{DY} d$ is again a descent direction: $g'^\top d' < 0$.

This is the induction step showing that the Dai–Yuan method produces descent directions at every
iteration under standard Wolfe line searches, whereas the Fletcher–Reeves method needs strong Wolfe
steps with $\sigma \le 1/2$ for this.

## Informally uses

- [The Dai–Yuan identity](inner-dai-yuan-direction.md): $g'^\top d' = \beta\, g^\top d$ with
  $\beta > 0$.
- [Wolfe curvature condition](../line-search-methods/curvature-condition.md): gives
  $d^\top (g' - g) > 0$, inequality (3.10) of the source.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, proof of Theorem 3.3, inequality (3.10).
