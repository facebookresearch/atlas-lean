# Projected stochastic gradient descent for convex Lipschitz learning problems

Let $K$ be a convex subset of a real inner product space with a projection $\pi$ onto $K$ that does not increase distances to points of $K$ (or $K$ the whole space and $\pi$ the identity), $\ell(\cdot, z)$ convex on $K$ for each $z$, and $g(x, z)$ a subgradient of $\ell(\cdot, z)$ at $x \in K$ relative to $K$ with $\|g(x,z)\| \le \rho$ for some $\rho > 0$, all measurable, and $\ell(x_0, \cdot)$ integrable. Run projected SGD on $T \ge 1$ i.i.d. examples $z_0, \dots, z_{T-1} \sim D$: $x_{t+1} = \pi(x_t - \eta\, g(x_t, z_t))$ with $\eta = B/(\rho\sqrt{T})$. Then for every $u \in K$ with $\|x_0 - u\| \le B$,

$$
\mathbb{E}\Big[L_D\Big(\frac{1}{T}\sum_{t<T} x_t\Big)\Big] \le L_D(u) + \frac{B\rho}{\sqrt{T}}.
$$

## Proof sketch

SGD is online gradient descent on the losses $\ell(\cdot, z_t)$, whose regret against $u$ is at most $B\rho\sqrt{T}$ with this step size. Since $x_t$ depends only on $z_0, \dots, z_{t-1}$, the online-to-batch conversion and Jensen's inequality turn the regret bound into the bound on the expected true risk of the averaged iterate.

## Depends on

- [Online-to-batch conversion](../../online-learning-and-boosting/online-to-batch-conversion.md)
- [Convergence of stochastic gradient descent](../../../../Analysis/convex-analysis-and-variations/gradient-descent/integral-sgd-average-sub-le.md)
- [SGD rates and learnability of convex-Lipschitz-bounded problems](../../pac-learning/learnability-of-convex-problems/sgd-rates-and-learnability-of-convex-lipschitz-bounded-probl.md)

## Proof depends on

- [Online-to-batch conversion](../../online-learning-and-boosting/online-to-batch-conversion.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
