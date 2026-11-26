# Scalar Gaussian Kernel KLReal

For real numbers $m, N, V$ and a measure $\mu$ on $\mathbb{R}$, the scalar Gaussian channel kernel divergence closed form (in nats) is

$$G(m, N, V, \mu) = \frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \int (x - m)^2 \, d\mu(x)}{V} - 1\right).$$

It is defined for all inputs, with the conventions $x / 0 = 0$, $\log 0 = 0$, $\log x = \log \lvert x \rvert$ for $x < 0$, and the integral taken to be $0$ when $(x - m)^2$ is not $\mu$-integrable.
