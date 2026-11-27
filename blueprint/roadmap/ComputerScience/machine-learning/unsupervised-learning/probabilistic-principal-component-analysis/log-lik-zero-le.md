# No latent factors: the noise-variance MLE is the average sample variance

Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data with sample mean $\bar{x}$ and sample covariance $S$,
and suppose $\operatorname{tr} S > 0$. Then for every $\mu \in \mathbb{R}^d$ and every real
$\sigma^2 > 0$, the probabilistic PCA log-likelihood of the data with the zero $d \times q$
loading matrix at $(\mu, 0, \sigma^2)$ is at most its value at
$(\bar{x}, 0, \operatorname{tr} S / d)$.

Here $\operatorname{tr} S / d$ is the average sample variance (Tipping and Bishop's $\sigma^2$
estimate with no retained components).
