# Gaussian Kernel KLReal scalar Coord

Let $\iota : \mathbb{R} \to \mathbb{R}^1$ be the linear isometry onto one-dimensional Euclidean space sending $x$ to the vector $(x)$ whose only coordinate is $x$.

For all real numbers $m, N, V$ and every measure $\mu$ on $\mathbb{R}$, the vector Gaussian kernel divergence closed form at gain $H = (1)$, reference mean $\iota(m)$, noise covariance $(N)$, reference covariance $(V)$ and input law $\iota_* \mu$,

$$\frac{1}{2}\left(\log\frac{\det (V)}{\det (N)} - 1 + \operatorname{tr}\big((V)^{-1} (N)\big) + \int (H y - \iota(m))^{\top} (V)^{-1} (H y - \iota(m)) \, d(\iota_*\mu)(y)\right),$$

equals the scalar closed form

$$\frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \int (x - m)^2 \, d\mu(x)}{V} - 1\right).$$

Both sides use the conventions $x / 0 = 0$, $\log 0 = 0$, $\log t = \log \lvert t \rvert$ for $t < 0$, a singular matrix has inverse $0$, and a non-integrable integrand has integral $0$.
