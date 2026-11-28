# Exact size of the one-sided z test

Let $n \ge 1$ and let $\mathcal N(\mu, v)^{\otimes n}$ denote the law of an i.i.d. sample of size $n$ from the normal law with mean $\mu$ and variance $v > 0$. For $x \in \mathbb{R}^n$, $\mu_0 \in \mathbb{R}$ and $v > 0$, write $z(x) = \sqrt n\,(\bar x - \mu_0)/\sqrt v$ for the known-variance z statistic, $\bar x = \frac1n\sum_i x_i$, and $\Phi$ for the standard normal distribution function. For $\alpha \in (0,1)$ and the cutoff $c = \Phi^{-1}(1 - \alpha)$, the rejection probability at the null mean is exactly $\alpha$:

$$\mathcal N(\mu_0, v)^{\otimes n}\big(z > \Phi^{-1}(1 - \alpha)\big) = \alpha.$$
