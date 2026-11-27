# Expected error of robust stochastic approximation (mirror descent SA)

Let $E$ be a finite-dimensional real normed space, $X \subseteq E$ compact, $X^o \subseteq X$, $\alpha > 0$, and let the distance-generating function $\omega$ satisfy $V_x(u) \ge \tfrac{\alpha}{2}\|u - x\|^2$ for $x \in X^o$, $u \in X$. Let $P \colon E \times E^* \to E$ be a measurable prox mapping: for $x \in X^o$, $P(x, \xi) \in X^o$ satisfies the optimality condition of $\operatorname{argmin}_{u \in X}\{\xi(u) + V_x(u)\}$. Let $f$ be convex and continuous on $X$, let $\xi_0, \xi_1, \ldots$ be independent random variables with common law $\nu$, and let $G \colon E \times \Xi \to E^*$ be jointly measurable with $\|G(x, \zeta)\|_* \le M$ for $x \in X$ and with mean $\int G(x, \zeta)\,d\nu(\zeta)$ a subgradient of $f$ at every $x \in X$ relative to $X$. Run

$$
x_{t+1} = P\big(x_t, \gamma_t G(x_t, \xi_t)\big)
$$

from a deterministic $x_0 \in X^o$ with steps $\gamma_t > 0$. Then for every $x^\star \in X$ with $V_{x_0}(x^\star) \le D^2$ and every $N \ge 1$, the weighted average $\tilde x_N = \big(\sum_{t<N} \gamma_t\big)^{-1}\sum_{t<N} \gamma_t x_t$ satisfies

$$
\mathbb{E}\big[f(\tilde x_N)\big] - f(x^\star) \le \frac{D^2 + \frac{M^2}{2\alpha}\sum_{t<N} \gamma_t^2}{\sum_{t<N} \gamma_t} .
$$

With the constant step $\gamma_t = \sqrt{2\alpha}\,D/(M\sqrt{N})$ the bound is $\sqrt{2}\,DM/\sqrt{\alpha N}$, the $O(N^{-1/2})$ rate that, unlike classical stochastic approximation with steps $\propto 1/t$, requires neither strong convexity nor a finely tuned step. The proof takes expectations of the [pathwise bound](stochastic-mirror-descent-average-le.md) in its telescoped form: $x_t$ is a measurable function of $\xi_0, \ldots, \xi_{t-1}$, hence independent of $\xi_t$, and Fubini's theorem gives $\mathbb{E}[G(x_t, \xi_t)(x_t - x^\star)] = \mathbb{E}[g(x_t)(x_t - x^\star)] \ge \mathbb{E}[f(x_t)] - f(x^\star)$ with $g$ the mean subgradient; Jensen's inequality passes to the average.

The source assumes only the second-moment bound $\mathbb{E}\|G(x, \xi)\|_*^2 \le M_*^2$ (2.40); the statement here assumes the stronger almost-sure bound $\|G\|_* \le M$, and i.i.d. noise.

## Background

- [Convergence of stochastic gradient descent](../gradient-descent/integral-sgd-average-sub-le.md): the Euclidean case with decreasing steps, proved the same way.

## Sources

- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, efficiency estimate (2.44), with $x_0 = \operatorname{argmin}_X \omega$ and $D = D_{\omega,X}$ of (2.43), so that $V_{x_0} \le D^2$ on $X$ by (2.42); the constant step is (2.45)–(2.46).
