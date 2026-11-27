# Scalar Gaussian Kernel KLReal dirac

For all real numbers $m, N, V, a$, the scalar Gaussian channel kernel closed form at the point-mass input $\delta_a$ is

$$\frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \int (x - m)^2 \, d\delta_a(x)}{V} - 1\right) = \frac{1}{2}\left(\log\frac{V}{N} + \frac{N + (a - m)^2}{V} - 1\right),$$

the scalar Gaussian divergence closed form of $\mathcal{N}(a, N)$ from $\mathcal{N}(m, V)$, that is, of $\mathrm{KL}(\mathcal{N}(a, N) \,\|\, \mathcal{N}(m, V))$ (with $x/0 = 0$ and $\log 0 = 0$).
