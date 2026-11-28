# Integrable llr comp Prod noise Kernel

Let $\kappa$ and $\iota$ be finite index sets, with input space $\mathbb{R}^{\kappa}$ and output space $\mathbb{R}^{\iota}$ of dimension $d = \lvert \iota \rvert$, both Euclidean, and let $H$ be a real $\iota \times \kappa$ matrix. Write $\mathcal{N}(m, S)$ for the Gaussian measure with mean $m$ and covariance matrix $S$.

Let $q \in \mathbb{R}^{\iota}$, let $R, T$ be positive definite real $\iota \times \iota$ matrices, and let $\mu$ be a probability measure on $\mathbb{R}^{\kappa}$ with finite second moment. Let $k$ be the additive Gaussian noise kernel sending $x \in \mathbb{R}^{\kappa}$ to the law of $H x + Z$ with $Z \sim \mathcal{N}(0, R)$, that is, $k(x) = \mathcal{N}(H x, R)$. Then the log-likelihood ratio $\log \frac{d(\mu \otimes k)}{d(\mu \times \mathcal{N}(q, T))}$ is integrable with respect to $\mu \otimes k$.
