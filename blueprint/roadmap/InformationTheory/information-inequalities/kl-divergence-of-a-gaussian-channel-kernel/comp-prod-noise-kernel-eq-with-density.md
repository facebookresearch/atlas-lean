# Comp Prod noise Kernel eq with Density

Let $\kappa$ and $\iota$ be finite index sets, with input space $\mathbb{R}^{\kappa}$ and output space $\mathbb{R}^{\iota}$ of dimension $d = \lvert \iota \rvert$, both Euclidean, and let $H$ be a real $\iota \times \kappa$ matrix. Write $\mathcal{N}(m, S)$ for the Gaussian measure with mean $m$ and covariance matrix $S$.

Let $R$ be a positive definite real $\iota \times \iota$ matrix and $\mu$ a probability measure on $\mathbb{R}^{\kappa}$. Let $k$ be the additive Gaussian noise kernel sending $x \in \mathbb{R}^{\kappa}$ to the law of $H x + Z$ with $Z \sim \mathcal{N}(0, R)$, that is, $k(x) = \mathcal{N}(H x, R)$. Then the joint law $\mu \otimes k$ has density

$$(x, y) \mapsto p_{Hx, R}(y) = \frac{1}{(2\pi)^{d/2} \sqrt{\det R}} \exp\left(-\frac{(y - Hx)^{\top} R^{-1} (y - Hx)}{2}\right)$$

with respect to $\mu \times \lambda$, where $\lambda$ is Lebesgue measure on $\mathbb{R}^{\iota}$.
