# Mean and second-moment bounds for discrete Gaussians above twice the smoothing parameter

Let $0 < \varepsilon < 1$, $s \ge 2\eta_\varepsilon(L)$, $c$ a center and $u$ a unit vector, with $L$ full rank in dimension $n$. For $x \leftarrow D_{L,s,c}$:

$$\bigl|\mathbb{E}\langle x - c, u\rangle\bigr| \le \frac{\varepsilon}{1-\varepsilon}s, \qquad \Bigl|\mathbb{E}\langle x - c, u\rangle^2 - \frac{s^2}{2\pi}\Bigr| \le \frac{\varepsilon}{1-\varepsilon}s^2,$$

$$\bigl\|\mathbb{E}[x - c]\bigr\|^2 \le \Bigl(\frac{\varepsilon}{1-\varepsilon}\Bigr)^2 s^2 n, \qquad \mathbb{E}\|x - c\|^2 \le \Bigl(\frac{1}{2\pi} + \frac{\varepsilon}{1-\varepsilon}\Bigr)s^2 n.$$

## Proof sketch

Compute the moments of the continuous Gaussian and compare via Poisson summation: the Fourier transforms of $x\rho_s(x)$ and $x^2\rho_s(x)$ on the dual lattice are bounded by the dual Gaussian mass at width $2/s$, which is at most $\varepsilon$ when $s \ge 2\eta_\varepsilon(L)$. The norm bounds follow by summing over an orthonormal basis.

## Depends on

- [Smoothing parameter of a lattice](smoothing-parameter.md)

## Sources

- D. Micciancio and O. Regev, "Worst-Case to Average-Case Reductions Based on Gaussian Measures", SIAM Journal on Computing 37(1), 2007.
