# Prod multivariate Gaussian eq with Density

Let $\iota$ be a finite index set with $d = \lvert \iota \rvert$, let $q \in \mathbb{R}^{\iota}$, let $T$ be a positive definite real $\iota \times \iota$ matrix, let $\kappa$ be a finite index set, and let $\mu$ be a probability measure on the input space $\mathbb{R}^{\kappa}$. Then the product $\mu \times \mathcal{N}(q, T)$ has density

$$(x, y) \mapsto p_{q, T}(y) = \frac{1}{(2\pi)^{d/2} \sqrt{\det T}} \exp\left(-\frac{(y - q)^{\top} T^{-1} (y - q)}{2}\right)$$

with respect to $\mu \times \lambda$, where $\lambda$ is Lebesgue measure on $\mathbb{R}^{\iota}$.
