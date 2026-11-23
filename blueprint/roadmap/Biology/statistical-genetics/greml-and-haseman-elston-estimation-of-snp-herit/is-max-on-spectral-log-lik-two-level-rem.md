# Closed form maximizes the spectral criterion for positive class means

Let $r$ be a finite index set, $d, w \in \mathbb{R}^r$ and $a \ne b$ reals such that every $d_i$ is
$a$ or $b$, and suppose both [class means](group-mean.md) $m_a$ and $m_b$ of $w_i^2$ are positive
(so both values occur). Let $\hat\theta$ be the [closed-form estimate](two-level-reml.md) and
$\ell$ the [spectral REML criterion](spectral-log-lik.md). Then for every
$\theta = (\sigma_g^2, \sigma_e^2)$ at which every [contrast variance](contrast-var.md)
$\sigma_g^2 d_i + \sigma_e^2$ is positive,

$$\ell(\theta) \le \ell(\hat\theta),$$

with equality only if $\theta = \hat\theta$. The contrast variances at $\hat\theta$ are $m_a$ and
$m_b$ ([class variances](contrast-var-two-level-reml.md)), so $\hat\theta$ lies in this region and
is the unique maximizer of $\ell$ there.
