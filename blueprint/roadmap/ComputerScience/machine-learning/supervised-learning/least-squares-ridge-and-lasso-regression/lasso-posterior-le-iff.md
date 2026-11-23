# Lasso is MAP estimation

Let $X$ be a real matrix with $m$ rows and columns indexed by a
finite set $\iota$, let $y \in \mathbb{R}^m$, and let $v > 0$ and $b > 0$. Let $P$ be the
posterior kernel of linear regression with Gaussian noise of variance $v$ and the Laplace prior
with scale $b$ on each coordinate, and let $\ell$ be the lasso objective with $\lambda = 2v/b$,
$\ell(\theta) = \sum_k (y_k - (X\theta)_k)^2 + \lambda \sum_{i \in \iota} |\theta_i|$. Then for all
$\theta, \theta' \in \mathbb{R}^\iota$, $P(\theta) \le P(\theta')$ if and only if
$\ell(\theta') \le \ell(\theta)$.
