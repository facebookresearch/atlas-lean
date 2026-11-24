# Uniform bound on the expected site-frequency spectrum

For real $\theta, \sigma$ and natural numbers $1 \le i < n$,

$$\bigl|\mathbb{E}\xi_i(\theta, \sigma)\bigr| \le |\theta| \binom{n}{i},$$

where $\mathbb{E}\xi_i(\theta, \sigma) = \int_0^1 \binom{n}{i} x^i (1 - x)^{n-i} \varphi_{\theta,\sigma}(x) \, dx$ is, for $\theta \ge 0$, the expected number of sites with $i$ derived copies in a sample of $n$ under the Poisson random field, with frequency density $\varphi_{\theta,\sigma}(x) = \theta\, u_\sigma(1 - x) / (x(1 - x))$, $u_\sigma(y) = (1 - e^{-2\sigma y})/(1 - e^{-2\sigma})$ for $\sigma \ne 0$ and $u_0(y) = y$ (with $a/0 = 0$). The bound is uniform in the scaled selection coefficient $\sigma$.
