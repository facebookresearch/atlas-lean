# Bridge to the canonical Weibull law

Let $k > 0$ and $\lambda > 0$, let $S$ be the Weibull survival function ($S(x) = 1$ for $x < 0$, $S(x) = e^{-(x/\lambda)^k}$ for $x \ge 0$), and let $W_{k,\lambda}$ be the Weibull distribution with shape $k$ and scale $\lambda$, which has density $\frac{k}{\lambda} (x/\lambda)^{k-1} e^{-(x/\lambda)^k}$ for $x > 0$ and $0$ for $x \le 0$. Then for every $x \in \mathbb{R}$,

$$S(x) = W_{k,\lambda}\bigl( (x, \infty) \bigr).$$

For $x < 0$ both sides are $1$, since $W_{k,\lambda}$ puts no mass on $(-\infty, 0]$.
