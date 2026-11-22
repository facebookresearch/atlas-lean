# Rate of mirror descent for the weighted average

In the setting of the [best-iterate rate](mirror-descent-exists-le.md), if moreover $f$ is convex on $X$, then for every $x^\star \in X$ and $N \ge 1$ the weighted average $\bar x_N = \big(\sum_{t<N} \gamma_t\big)^{-1} \sum_{t<N} \gamma_t x_t$ satisfies

$$
f(\bar x_N) - f(x^\star) \le \frac{V_{x_0}(x^\star) + \frac{L^2}{2\alpha} \sum_{t<N} \gamma_t^2}{\sum_{t<N} \gamma_t} .
$$

The proof sums the subgradient inequalities with weights $\gamma_t$ and applies Jensen's inequality to the average.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, Proposition 5.1(i), inequality (5.8), for the averaged iterate $\bar x_t$ (with $\alpha = 1$).
