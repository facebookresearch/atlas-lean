# Mirror descent

Mirror descent (Nemirovski and Yudin, 1983) is the subgradient method with the Euclidean geometry replaced by a *proximal setup*: a norm $\|\cdot\|$ on the space, with dual norm $\|\cdot\|_*$ for the subgradients, and a distance-generating function $\omega$ that is strongly convex with respect to that norm. A step moves from $x_t$ to the prox point $x_{t+1} = \operatorname{argmin}_{u \in X}\{\gamma_t \langle g_t, u\rangle + V_{x_t}(u)\}$ of the [Bregman divergence](bregman.md) $V$. One inequality drives everything: the [one-step bound](bregman-prox-step-le.md), obtained from the optimality condition of the prox step by the [three-point identity](bregman-three-point.md), telescopes to a [regret bound](mirror-descent-sum-le.md) for arbitrary linear forms $g_t$. With subgradients of a convex Lipschitz function it gives the rates for the [best](mirror-descent-exists-le.md) and the [averaged](mirror-descent-average-le.md) iterate and, with a constant step, the efficiency estimate $\sqrt{2\Omega}L/\sqrt{N}$ ([constant-step rate](mirror-descent-exists-le-sqrt.md)), which, on $\ell_1$ and $\ell_2$ balls with the matching setups, no black-box first-order method can improve by more than a logarithmic factor while the number of steps stays below the dimension. With noisy subgradients it gives the [pathwise bound](stochastic-mirror-descent-average-le.md) of robust stochastic approximation (Nemirovski, Juditsky, Lan and Shapiro, 2009) and, in expectation, its [efficiency estimate](integral-robust-sa-average-sub-le.md).

The Euclidean setup $\omega = \tfrac12\|\cdot\|_2^2$ recovers the projected subgradient method. On the simplex, the $\ell_1$ norm with the [entropy](entropy.md) gives the Kullback–Leibler divergence, strong convexity by Pinsker's inequality, an $\omega$-diameter $\log n$, and the prox step is the multiplicative-weights update, so that the [entropic rate](entropic-mirror-descent-exists-le.md) depends on the dimension only through $\sqrt{\log n}$. Against the vertices of the simplex the telescoped bound gives a [regret bound for prediction with expert advice](multiplicative-weights-regret-le.md), $\log n/\gamma + \gamma N/2$ for losses in $[-1, 1]$.

The results assume strong convexity in the Bregman form $V_x(u) \ge \tfrac{\alpha}{2}\|u - x\|^2$ and that each prox point exists, and use each prox step only through its first-order optimality condition.

## The proximal setup

- [Bregman divergence (prox-function) of a distance-generating function](bregman.md)
- [Three-point identity for Bregman divergences](bregman-three-point.md)
- [One-step inequality of mirror descent](bregman-prox-step-le.md)

## Rates of mirror descent

- [Telescoped mirror descent bound](mirror-descent-sum-le.md)
- [Rate of mirror descent for the best iterate](mirror-descent-exists-le.md)
- [Rate of mirror descent for the weighted average](mirror-descent-average-le.md)
- [Constant-step rate of mirror descent](mirror-descent-exists-le-sqrt.md)
- [Pathwise bound of stochastic mirror descent](stochastic-mirror-descent-average-le.md)
- [Expected error of robust stochastic approximation (mirror descent SA)](integral-robust-sa-average-sub-le.md)

## The entropy setup on the simplex

- [The space $\mathbb{R}^n$ with the $\ell_1$ norm](l1.md)
- [The probability simplex](simplex.md)
- [The relative interior of the simplex](pos-simplex.md)
- [The uniform point of the simplex](uniform.md)
- [The entropy distance-generating function](entropy.md)
- [Derivative of the entropy](entropy-deriv.md)
- [The linear form with coordinates $c$](linear-form.md)
- [The Bregman divergence of the entropy is the Kullback–Leibler divergence](bregman-entropy-eq.md)
- [Strong convexity of the entropy on the simplex with respect to $\|\cdot\|_1$](bregman-entropy-ge.md)
- [The $\omega$-diameter of the simplex under the entropy is at most $\log n$](bregman-entropy-uniform-le.md)
- [Coordinate bound on the dual norm of a linear form on $\ell_1$](norm-le-of-abs-apply-single-le.md)
- [The prox step of the entropy is the multiplicative-weights update](entropy-prox-multiplicative.md)
- [Rate of entropic mirror descent on the simplex](entropic-mirror-descent-exists-le.md)
- [Regret of entropic mirror descent for prediction with expert advice](multiplicative-weights-regret-le.md)

## Related topics

- [Gradient descent](../gradient-descent/README.md): the Euclidean subgradient method and stochastic gradient descent, the Euclidean special cases.
- [Hedge algorithm](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/README.md): the multiplicative-weights update, which is the entropic prox step; its regret bounds there follow from a potential argument.
- [Information inequalities](../../../InformationTheory/information-inequalities/README.md): Pinsker's inequality, which gives the strong convexity of the entropy with respect to $\|\cdot\|_1$.
- [Accelerated gradient methods](../accelerated-gradient-methods/README.md): the accelerated method couples a gradient step with a weighted mirror-descent step, and its continuous-time limit is generated by a Lagrangian built on the Bregman divergence.
