# Log-density of the multivariate Gaussian

Let $J$ be a finite set with $n$ elements, let
$\mu, x \in \mathbb{R}^J$, let $S$ be a positive definite real $J \times J$ matrix, and write
$\mathcal{N}(x \mid \mu, S)$ for the multivariate Gaussian density at $x$ with mean $\mu$ and
covariance $S$. Then $\log \mathcal{N}(x \mid \mu, S) = -\frac{n}{2} \log (2\pi) -
\frac{1}{2} \log \det S - \frac{1}{2} (x - \mu)^{\mathsf T} S^{-1} (x - \mu)$.
