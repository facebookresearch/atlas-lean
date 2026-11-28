# Zinkevich's regret bound for online gradient descent

Let $E$ be a real inner product space, $\eta > 0$, $x^* \in E$, $P : E \to E$ a 1-Lipschitz map with $P(x^*) = x^*$, and for each round $t$ let $f_t : E \to \mathbb{R}$ and $g_t : E \to E$ satisfy

$$f_t(x) + \langle g_t(x), x^* - x \rangle \le f_t(x^*) \quad \text{for every } x \in E.$$

Let $x_0 \in E$ and $x_{t+1} = P(x_t - \eta\, g_t(x_t))$. Then for every $T$,

$$\sum_{t=0}^{T-1} \big(f_t(x_t) - f_t(x^*)\big) \le \frac{\|x_0 - x^*\|^2}{2\eta} + \frac{\eta}{2} \sum_{t=0}^{T-1} \|g_t(x_t)\|^2.$$

No idempotence of $P$ and no inequality at comparators other than $x^*$ is assumed. The usual setting, a projection onto a closed convex set containing $x^*$ with $g_t(x)$ a subgradient of a convex $f_t$ at $x$, satisfies these hypotheses.
