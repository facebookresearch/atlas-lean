# Bang-bang optimal ergodic harvesting of a population in a random environment

Let the population density follow

$$
dX(t) = X(t)\big(\mu(X(t)) - h(t)\big)\,dt + \sigma X(t)\,dB(t), \qquad X(0) = x > 0,
$$

where $B$ is a Brownian motion, $\sigma > 0$, the per-capita growth rate $\mu$ is locally Lipschitz and decreasing with $\mu(x) \to -\infty$ as $x \to \infty$, and $x\mu(x)$ has a unique maximum. The harvesting rate $h(t) \in [0, M]$ is any process adapted to the Brownian filtration. With a yield function $\Phi$ (continuous, $\Phi(0) = 0$), the goal is to maximize the asymptotic yield

$$
\liminf_{T\to\infty} \frac1T \int_0^T \Phi\big(X(t)h(t)\big)\,dt .
$$

**Theorem.** Suppose the unharvested population persists, $\mu(0) - \sigma^2/2 > 0$.

1. For the linear yield $\Phi(x) = x$, there is a threshold $x^* \in (0,\infty)$ such that the optimal strategy is the stationary Markov bang-bang control $v(x) = 0$ for $x \le x^*$ and $v(x) = M$ for $x > x^*$; it achieves the optimal yield $\rho^*$ almost surely against every admissible strategy, and $\rho^* \le \sup_{x \ge 0} x\mu(x)$, the deterministic maximum sustainable yield.
2. If $\Phi \in C^1$ is weakly convex and grows at most polynomially, the optimal strategy is again bang-bang (harvest at rate $0$ or $M$), and it has a single threshold $x^*$ as above if moreover $G(x) = \Phi(xM)\big(1 - \tfrac{2}{\sigma^2}\mu(x)\big) - xM\,\Phi'(xM)$ has a unique extreme point in $(0,\infty)$, which is a minimum.
3. If $\Phi \in C^2$ is strictly concave, the optimal strategy is continuous: $v(x) = \min\{M, \max\{0, [\Phi']^{-1}(V^*_x(x))/x\}\}$, where $V^*$ solves the ergodic HJB equation $\max_{u \in [0,M]} [\mathcal{L}_u V(x) + \Phi(xu)] = \rho^*$ with $\mathcal{L}_u f = x(\mu(x) - u) f' + \tfrac12 \sigma^2 x^2 f''$.

## Expansion

Ergodic control theory gives an optimal stationary Markov strategy and a classical $C^2$ solution $V^*$ of the HJB equation with $V^*(1) = 0$ and $\rho = \rho^* > 0$. For linear yield the maximized expression is affine in $u$ with coefficient $x(1 - V^*_x(x))$, so the optimum is $u = M$ where $V^*_x < 1$ and $u = 0$ where $V^*_x > 1$; an analysis of the first-order ODE for $V^*_x$ bounds the number and direction of its crossings of the level $1$, which yields a single threshold. With concave yield the pointwise maximizer is interior, hence continuous. The bound by the deterministic MSY says environmental noise cannot increase the long-run harvest.

## Sources

- Alexandru Hening, Dang H. Nguyen, Sergiu C. Ungureanu and Tak Kwong Wong, *Asymptotic harvesting of populations in random environments*, arXiv:1710.01221, main theorem (Section 2), theorems on concave and convex yields (Section 3), and Theorems A.1 and A.2 (Appendix A). <https://doi.org/10.48550/arXiv.1710.01221> Published version: Journal of Mathematical Biology,Vol. 78, Issue 1-2, 293-329, 2019.
