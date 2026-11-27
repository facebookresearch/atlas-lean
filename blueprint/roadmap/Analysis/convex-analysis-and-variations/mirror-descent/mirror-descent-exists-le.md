# Rate of mirror descent for the best iterate

In the setting of the [telescoped bound](mirror-descent-sum-le.md), let $f \colon E \to \mathbb{R}$, let each $g_t$ be a subgradient of $f$ at $x_t$ relative to $X$ ($f(x_t) + g_t(y - x_t) \le f(y)$ for $y \in X$) with $\|g_t\|_* \le L$, and let all $\gamma_t > 0$. Then for every $x^\star \in X$ and $N \ge 1$ some iterate $t < N$ satisfies

$$
f(x_t) - f(x^\star) \le \frac{V_{x_0}(x^\star) + \frac{L^2}{2\alpha} \sum_{t<N} \gamma_t^2}{\sum_{t<N} \gamma_t} .
$$

With divergent steps $\gamma_t \to 0$, $\sum \gamma_t = \infty$ the right-hand side tends to $0$.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, Proposition 5.1(i), inequality (5.8), for the best iterate $\hat x_t$ (with $\alpha = 1$).
