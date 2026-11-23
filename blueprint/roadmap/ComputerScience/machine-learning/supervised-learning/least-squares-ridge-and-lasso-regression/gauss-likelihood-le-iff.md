# The Gaussian likelihood decreases with the residual sum of squares

Let $X$ be a real
matrix with $m$ rows and columns indexed by a finite set $\iota$, let $y \in \mathbb{R}^m$ and
$v > 0$, let $L$ be the Gaussian likelihood of linear regression with noise variance $v$, and let
$\mathrm{RSS}(\theta) = \sum_k (y_k - (X\theta)_k)^2$ be the residual sum of squares. Then for all
$\theta, \theta' \in \mathbb{R}^\iota$, $L(\theta) \le L(\theta')$ if and only if
$\mathrm{RSS}(\theta') \le \mathrm{RSS}(\theta)$.
