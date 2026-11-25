# Local exponential stability of the squid resting state

For the [squid parameters](squid.md) there are $\delta > 0$, $K > 0$ and $\alpha > 0$ such that,
writing $x^*$ for the [resting state](rest.md) and $\|\cdot\|$ for the maximum norm on
$\mathbb{R}^4$, every initial state $x_0$ with $\|x_0 - x^*\| < \delta$ has the following two
properties.

- There is a [solution](is-solution.md) $x$ on $[0, \infty)$ with $x(0) = x_0$.
- Every such solution satisfies $\|x(t) - x^*\| \le K e^{-\alpha t}\,\|x_0 - x^*\|$ for all
  $t \ge 0$.

This follows by linearization from the [Hurwitz Jacobian at rest](jac-squid-rest-is-hurwitz.md).
