# Mem Lp comp Prod noise Kernel

Let $\kappa$ and $\iota$ be finite index sets, with input space $\mathbb{R}^{\kappa}$ and output space $\mathbb{R}^{\iota}$ of dimension $d = \lvert \iota \rvert$, both Euclidean, and let $H$ be a real $\iota \times \kappa$ matrix. Write $\mathcal{N}(m, S)$ for the Gaussian measure with mean $m$ and covariance parameter $S$ (the point mass $\delta_m$ when $S$ is not positive semidefinite), so the statement holds for every real matrix $R$.

Let $q \in \mathbb{R}^{\iota}$, let $R$ be a real $\iota \times \iota$ matrix, and let $\mu$ be a probability measure on $\mathbb{R}^{\kappa}$ with finite second moment. Let $k$ be the additive Gaussian noise kernel sending $x \in \mathbb{R}^{\kappa}$ to the law of $H x + Z$ with $Z \sim \mathcal{N}(0, R)$, that is, $k(x) = \mathcal{N}(H x, R)$. Then under the joint law $\mu \otimes k$ both the noise $(x, y) \mapsto y - Hx$ and the output deviation $(x, y) \mapsto y - q$ are in $L^2$.
