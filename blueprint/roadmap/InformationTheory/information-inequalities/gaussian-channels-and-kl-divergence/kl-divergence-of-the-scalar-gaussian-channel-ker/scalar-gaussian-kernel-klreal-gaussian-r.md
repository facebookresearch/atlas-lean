# Scalar Gaussian Kernel KLReal gaussian Real

For real numbers $m, N, V, \mu_0$ and a variance $s \ge 0$, the scalar Gaussian channel kernel closed form at the Gaussian input $\mathcal{N}(\mu_0, s)$ is

$$\frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \big(s + (\mu_0 - m)^2\big)}{V} - 1\right),$$

since $\int (x - m)^2 \, d\mathcal{N}(\mu_0, s)(x) = s + (\mu_0 - m)^2$ (conventions $x/0 = 0$, $\log 0 = 0$, and $\log t = \log \lvert t \rvert$ for $t < 0$).
