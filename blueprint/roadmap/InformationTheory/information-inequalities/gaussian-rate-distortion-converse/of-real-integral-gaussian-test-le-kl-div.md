# Of Real integral gaussian Test le kl Div product Marginal

Let $D > 0$, $\sigma^2 > 0$, and let $\mu$ be a probability measure on $\mathbb{R}^2$ that is distortion-feasible at level $D$ for the source variance $\sigma^2$. Then

$$\max\left(0, \int_{\mathbb{R}^2} t_{D, \sigma^2} \, d\mu\right) \le D_{\mathrm{KL}}\left(\mu \,\middle\|\, \mu_1 \otimes \mu_2\right),$$

with the divergence in nats and values in $[0, \infty]$. A probability measure $\mu$ on $\mathbb{R}^2$ is distortion-feasible at level $D$ for the source variance $\sigma^2$ if $D \ge 0$, the first marginal of $\mu$ is $\mathcal{N}(0, \sigma^2)$, and $\int (x - y)^2 \, d\mu(x, y) \le D$, the integral of a nonnegative function, possibly infinite. $\mu_1 \otimes \mu_2$ denotes the product of the marginals of $\mu$. Here $t_{D, \sigma^2}(x, y) = \ln \varphi_D(x - y) - \ln \varphi_{\sigma^2}(x)$ is the Gaussian test function, $\varphi_v$ being the centered Gaussian density with variance $v$ (with $\varphi_0 \equiv 0$ and $\ln 0 = 0$).
