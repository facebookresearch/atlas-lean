# Integral gaussian Test gt of integral sq error lt

Let $0 < D < \sigma^2$ and let $\mu$ be a probability measure on $\mathbb{R}^2$ that is distortion-feasible at level $D$ for the source variance $\sigma^2$, with expected square error strictly below $D$: $\int (x - y)^2 \, d\mu < D$. Then

$$\int_{\mathbb{R}^2} t_{D, \sigma^2} \, d\mu > \frac{1}{2} \ln \frac{\sigma^2}{D}.$$

A probability measure $\mu$ on $\mathbb{R}^2$ is distortion-feasible at level $D$ for the source variance $\sigma^2$ if $D \ge 0$, the first marginal of $\mu$ is $\mathcal{N}(0, \sigma^2)$, and $\int (x - y)^2 \, d\mu(x, y) \le D$, the integral of a nonnegative function, possibly infinite. Here $t_{D, \sigma^2}(x, y) = \ln \varphi_D(x - y) - \ln \varphi_{\sigma^2}(x)$ is the Gaussian test function, $\varphi_v$ being the Gaussian density for $v > 0$, extended by the zero function at $v = 0$, with $\ln 0 = 0$.
