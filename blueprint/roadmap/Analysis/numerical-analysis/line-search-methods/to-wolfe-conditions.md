# Strong Wolfe steps are standard Wolfe steps

A step length satisfying the [strong Wolfe conditions](strong-wolfe-conditions.md) with constants
$\delta, \sigma$ satisfies the [standard Wolfe conditions](wolfe-conditions.md) with the same
constants, since $\nabla f(x + \alpha d)^\top d \ge -|\nabla f(x + \alpha d)^\top d| \ge
\sigma\, \nabla f(x)^\top d$. So every result proved under standard Wolfe steps, such as the
[Zoutendijk condition](zoutendijk.md), holds under strong Wolfe steps.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, compare conditions (1.8) and (1.10).
