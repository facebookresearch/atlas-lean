# Lasso objective

For a real matrix $X$ with $m$ rows and columns indexed by a finite set
$\iota$, responses $y \in \mathbb{R}^m$ and a real number $\lambda$, the lasso objective at
$\theta \in \mathbb{R}^\iota$ is
$\sum_{k=1}^m (y_k - (X\theta)_k)^2 + \lambda \sum_{i \in \iota} |\theta_i|$, the residual sum of
squares plus $\lambda$ times the $\ell^1$ norm of $\theta$.
