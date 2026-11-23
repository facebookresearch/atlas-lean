# The weighted Gaussian MLE for points in general position

Let $I$ be a nonempty finite
set and $J$ a finite set, and let $x_i \in \mathbb{R}^J$ ($i \in I$) be points with positive
weights $w_i > 0$ that do not all lie in an affine hyperplane: for every nonzero
$v \in \mathbb{R}^J$ there are $i, j \in I$ with
$\langle v, x_i \rangle \ne \langle v, x_j \rangle$. Let $m$ be their weighted mean and $C$ their
weighted scatter matrix about $m$ (the weighted sample covariance), and write
$\mathcal{N}(x \mid \mu, S)$ for the multivariate Gaussian density at $x$ with mean $\mu$ and
covariance $S$. Then for every $\mu \in \mathbb{R}^J$ and every positive definite real
$J \times J$ matrix $S$,
$\sum_{i \in I} w_i \log \mathcal{N}(x_i \mid \mu, S) \le
\sum_{i \in I} w_i \log \mathcal{N}(x_i \mid m, C)$.
