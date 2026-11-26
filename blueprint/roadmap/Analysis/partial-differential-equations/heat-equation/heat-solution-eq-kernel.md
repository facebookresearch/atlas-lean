# The one-dimensional heat solution as a heat-kernel convolution

For every $f : \mathbb{R} \to \mathbb{R}$ and all real $t$ and $x$, the [heat-kernel solution](heat-solution.md) $u(t, x)$ of $f$ equals

$$\int_{\mathbb{R}} \Phi(t, x - y)\, f(y) \, dy \quad (t > 0), \qquad f(x) \quad (t \le 0),$$

where $\Phi(t, z) = (4\pi t)^{-1/2} e^{-z^2/(4t)}$ is the [fundamental solution of the heat equation](heat-kernel.md) on $\mathbb{R}$. Both integrals are Lebesgue integrals, taken to be $0$ when the integrand is not integrable, so the identity holds for every $f$.
