# Closed form is the unique REML maximizer for positive class means

Let $m$ and $r$ be finite index sets, $K$ a real $m \times m$ matrix, $B$ a real $r \times m$
matrix with $BB^\top = I$ and $BKB^\top = \operatorname{diag}(d)$, $y \in \mathbb{R}^m$ and
$w = By$. Let $a \ne b$ be reals such that every $d_i$ is $a$ or $b$, and suppose both
[class means](group-mean.md) $m_a$ and $m_b$ of $w_i^2$ are positive. Let $\Theta$ be the set of
$\theta = (\sigma_g^2, \sigma_e^2)$ at which every [contrast variance](contrast-var.md)
$\sigma_g^2 d_i + \sigma_e^2$ is positive; it is where $B V(\theta) B^\top$ is positive definite,
for $V(\theta) = \sigma_g^2 K + \sigma_e^2 I$. Then the [closed-form estimate](two-level-reml.md)
$\hat\theta$ lies in $\Theta$, maximizes over $\Theta$ the restricted log-likelihood of $y$ for $B$
at $V(\theta)$ (the logarithm of the density of the Gaussian law $N(0, B V(\theta) B^\top)$ at
$By$), and is the only point of $\Theta$ where this maximum is attained.
