# Optimal dual solutions are supergradients of the LP value function

For $V(b) = \max\{c^{\mathsf T}x : Ax \le b,\ x \ge 0\}$, let $V(b)$ be finite and let $y$ be an optimal dual solution at $b$. Then $V(b') \le V(b) + y^{\mathsf T}(b' - b)$ for every $b'$, where $V(b') = -\infty$ when the perturbed problem is infeasible. So $y$ is a supergradient of the concave function $V$ at $b$. Differentiability of $V$ is treated separately.

## Proof depends on

- [Strong linear programming duality](strong-linear-programming-duality.md): an optimal dual solution exists and has value $V(b)$; weak duality at $b'$ gives the inequality.

## Background

- [Differentiability of the LP value function and shadow prices](differentiability-of-the-lp-value-function.md): the gradient statement at interior points.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, §5.6.2, inequality (5.57), applied to the minimization of $-c^{\mathsf T}x$
