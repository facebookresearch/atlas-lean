# Strong Wolfe conditions

A step length $\alpha$ along $d$ from $x$ satisfies the *strong Wolfe conditions* with constants
$\delta$ and $\sigma$ if it satisfies the [Armijo condition](armijo-condition.md) and

$$|\nabla f(x + \alpha d)^\top d| \le -\sigma\, \nabla f(x)^\top d,$$

usually with $0 < \delta < \sigma < 1$. The classical convergence analyses of the Fletcher–Reeves,
Polak–Ribière–Polyak and Hestenes–Stiefel conjugate gradient methods assume these conditions.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, conditions (1.7) and (1.8).
