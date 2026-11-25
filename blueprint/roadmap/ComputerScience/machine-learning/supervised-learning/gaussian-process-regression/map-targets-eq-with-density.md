# Density of the targets in Gaussian-process regression

Let $k$ be a kernel and $x = (x_j)_{j \in \nu}$ a finite family of $n = |\nu|$ training inputs whose kernel matrix $K = K(x, x)$ is positive semidefinite, and let $\sigma^2 > 0$. Let $f$ and $\varepsilon$ be independent measurable random vectors in $\mathbb{R}^\nu$ on a probability space with $f \sim N(0, K)$ and $\varepsilon \sim N(0, \sigma^2 I)$. Then the targets $y = f + \varepsilon$ have the density

$$\mathcal{N}(y \mid 0, K + \sigma^2 I) = (2\pi)^{-n/2} \det(K + \sigma^2 I)^{-1/2} \exp\big(-\tfrac12\, y^\top (K + \sigma^2 I)^{-1} y\big)$$

with respect to Lebesgue measure on $\mathbb{R}^\nu$. Viewed as a function of the hyperparameters for the observed $y$, this density is the marginal likelihood $p(y \mid x)$ of Rasmussen and Williams (2006), Equation 2.28.
