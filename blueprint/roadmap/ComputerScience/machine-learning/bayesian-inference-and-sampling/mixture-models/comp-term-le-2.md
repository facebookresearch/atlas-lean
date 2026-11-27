# The mean and covariance updates maximize each component term

Let
$x_1, \dots, x_N \in \mathbb{R}^d$ be data in general position (at least one point, and not all
in an affine hyperplane), let $\theta$ be valid mixture parameters with responsibilities
$r_{nk}$, and fix a component $k$. Write $\mathcal{N}(x \mid \mu, S)$ for the multivariate
Gaussian density and let $\mu'_k$ and $\Sigma'_k$ be the responsibility-weighted mean and the
responsibility-weighted sample covariance of the data for component $k$. Then for every
$\mu \in \mathbb{R}^d$ and every positive definite $d \times d$ matrix $S$,

$$\sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu, S) \le
\sum_n r_{nk} \log \mathcal{N}(x_n \mid \mu'_k, \Sigma'_k).$$
