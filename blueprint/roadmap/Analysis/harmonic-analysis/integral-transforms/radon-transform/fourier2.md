# Two-dimensional Fourier transform

For $f : \mathbb{R}^2 \to \mathbb{C}$ and
$k = (k_1, k_2) \in \mathbb{R}^2$, the Fourier transform of $f$ at $k$ is

$$\hat f(k) = \int_{\mathbb{R}^2} e^{-2\pi i (x_1 k_1 + x_2 k_2)} \, f(x) \, dx,$$

where $dx$ is Lebesgue measure on $\mathbb{R}^2$ and the integral is taken to be $0$ when the
integrand is not integrable.

For integrable $w : \mathbb{R}^2 \to \mathbb{C}$ and $\ell \in \mathbb{R}^2$, multiplication by
$e^{\pm 2\pi i\,\ell\cdot x}$ shifts the transform to $\hat w(k\mp\ell)$. For integrable $f$ and an
invertible real $2\times2$ matrix $M$, $\widehat{f\circ M}(k)=|\det M|^{-1}\hat f(M^{-\mathsf T}k)$.
These identities are recorded for exposition only.
