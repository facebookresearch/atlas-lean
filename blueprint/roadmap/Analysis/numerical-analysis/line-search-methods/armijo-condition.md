# Armijo sufficient decrease condition

Let $E$ be a real Hilbert space (for instance $\mathbb{R}^n$) and $f : E \to \mathbb{R}$. A step length $\alpha$ along a direction $d$ from $x$ satisfies the *Armijo* (sufficient
decrease) condition with constant $\delta$ if

$$f(x + \alpha d) \le f(x) + \delta\, \alpha\, \nabla f(x)^\top d.$$

For a descent direction ($\nabla f(x)^\top d < 0$) the condition asks for a decrease proportional
to the step and to the directional derivative. On its own it does not prevent arbitrarily short
steps; the [curvature condition](curvature-condition.md) does.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, condition (1.7).
