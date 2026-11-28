# Scalar Gaussian Kernel KLReal dirac

For all real numbers $m, N, V, a$, the scalar Gaussian channel kernel closed form at the point-mass input $\delta_a$ is

$$\frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \int (x - m)^2 \, d\delta_a(x)}{V} - 1\right) = \frac{1}{2}\left(\log\frac{V}{N} + \frac{N + (a - m)^2}{V} - 1\right),$$

an identity of real expressions for all real inputs, with $x/0 = 0$, $\log 0 = 0$ and $\log t = \log \lvert t \rvert$ for $t < 0$. When $N > 0$ and $V > 0$, the right side is the scalar Gaussian divergence closed form of $\mathcal{N}(a, N)$ from $\mathcal{N}(m, V)$, that is, $\mathrm{KL}(\mathcal{N}(a, N) \,\|\, \mathcal{N}(m, V))$.
