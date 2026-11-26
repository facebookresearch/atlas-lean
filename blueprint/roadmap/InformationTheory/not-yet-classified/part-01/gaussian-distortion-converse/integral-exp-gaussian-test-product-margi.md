# The exponentiated Gaussian test is normalized

Let $\sigma^2 \ge 0$ and $D \in \mathbb{R}$. The feasible set $\mathcal{F}(\sigma^2, D)$ consists of the probability measures $\mu$ on $\mathbb{R}^2$ with $D \ge 0$, first marginal $\mathcal{N}(0, \sigma^2)$, and $\int (x - \hat x)^2 \, d\mu(x, \hat x) \le D$ (a lower integral in $[0, \infty]$). For $D, \sigma^2 > 0$ let $\varphi_v$ denote the density of $\mathcal{N}(0, v)$ and define the Gaussian test $T(x, \hat x) = \log \varphi_D(x - \hat x) - \log \varphi_{\sigma^2}(x)$. For a law $\mu$ on $\mathbb{R}^2$ with marginals $\mu_1, \mu_2$, write $\mu_1 \otimes \mu_2$ for the product of its marginals.

Let $D > 0$, $\sigma^2 > 0$ and $\mu \in \mathcal{F}(\sigma^2, D)$. Then

$$\int e^{T(x, \hat x)} \, d(\mu_1 \otimes \mu_2)(x, \hat x) = 1.$$
