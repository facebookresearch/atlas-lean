# Negative logarithm of the Weibull survival function

Let $k, \lambda \in \mathbb{R}$ and let $S(x) = 1$ for $x < 0$ and $S(x) = \exp\bigl(-(x/\lambda)^k\bigr)$ for $x \ge 0$ be the Weibull survival function with shape $k$ and scale $\lambda$ (real powers, with $x / 0 = 0$). For every $x \ge 0$ and all $k, \lambda$,

$$-\log S(x) = (x/\lambda)^k.$$

The power-law cumulative hazard is part of the definition of $S$ (the assumed model), not a consequence of independence.

For shape $k > 0$ and scale $\lambda > 0$, $S$ is the survival function of the Weibull distribution. For other parameters it need not be a survival function: shape $1$, scale $-1$ and $x = 1$ give $S(1) = e > 1$. Here $x^y$ is the real power: $e^{y \log x}$ for $x > 0$, $\lvert x\rvert^y \cos(\pi y)$ for $x < 0$, and for $x = 0$ it is $1$ when $y = 0$ and $0$ otherwise.
