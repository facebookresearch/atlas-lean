# Differentiability of the LP value function and shadow prices

For $V(b) = \max\{c^{\mathsf T}x : Ax \le b, x \ge 0\}$, let $b$ lie in the interior of the set of right-hand sides where $V$ is finite. If $V$ is differentiable at $b$, then every optimal dual solution $y$ at $b$ equals $\nabla V(b)$, so the optimal dual solution is unique. The identification of the optimal dual set with the set of supergradients of $V$ at $b$, and the converse that a unique optimal dual solution forces differentiability, are stated on the page on optimal dual solutions as supergradients.

## Proof depends on

- [Optimal dual solutions are supergradients of the LP value function](lp-value-supporting-price-inequality.md): the supergradient inequality on both sides of $b$.

## Background

- [Optimal dual solutions are the supergradients of the LP value function](optimal-dual-solutions-are-the-supergradients-of-the-lp-value.md): the optimal dual set as the superdifferential and the converse.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, §5.6.3, formula (5.58)
