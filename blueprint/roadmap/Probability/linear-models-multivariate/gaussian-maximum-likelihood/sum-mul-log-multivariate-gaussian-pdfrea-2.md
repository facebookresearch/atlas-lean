# The weighted mean is the Gaussian MLE of the mean

Let $I$ and $J$ be finite sets, let
$x_i \in \mathbb{R}^J$ ($i \in I$) be points with real weights $w_i$ such that $\sum_i w_i > 0$,
let $m$ be their weighted mean, and let $S$ be a positive definite real $J \times J$ matrix.
Write $\mathcal{N}(x \mid \mu, S)$ for the multivariate Gaussian density at $x$ with mean $\mu$
and covariance $S$. Then for every $\mu \in \mathbb{R}^J$,
$\sum_{i \in I} w_i \log \mathcal{N}(x_i \mid \mu, S) \le
\sum_{i \in I} w_i \log \mathcal{N}(x_i \mid m, S)$.
