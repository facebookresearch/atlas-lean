# Gaussian Kernel KLReal

Let $\kappa$ and $\iota$ be finite index sets with $d = \lvert \iota \rvert$, let $H$ be a real $\iota \times \kappa$ matrix, $q \in \mathbb{R}^{\iota}$, $R, T$ real $\iota \times \iota$ matrices, and $\mu$ a measure on $\mathbb{R}^{\kappa}$. The Gaussian channel kernel divergence closed form is

$$\frac{1}{2}\left(\log\frac{\det T}{\det R} - d + \operatorname{tr}(T^{-1} R) + \int (H x - q)^{\top} T^{-1} (H x - q) \, d\mu(x)\right)$$

It is defined for all inputs, with the conventions $x/0 = 0$, $\log 0 = 0$, $\log x = \log \lvert x \rvert$ for $x < 0$, $T^{-1} = 0$ for singular $T$, and the integral equal to $0$ when the integrand is not $\mu$-integrable.
