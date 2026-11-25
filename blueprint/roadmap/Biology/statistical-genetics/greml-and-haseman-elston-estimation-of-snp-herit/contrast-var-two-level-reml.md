# Contrast variances at the closed-form estimate equal the class means

Let $r$ be a finite index set, $d, w \in \mathbb{R}^r$ and $a \ne b$ reals, and let
$\hat\theta = (\hat\sigma_g^2, \hat\sigma_e^2)$ be the [closed-form estimate](two-level-reml.md),
$\hat\sigma_g^2 = (m_a - m_b)/(a - b)$ and $\hat\sigma_e^2 = (a m_b - b m_a)/(a - b)$, where $m_a$
and $m_b$ are the [class means](group-mean.md) of $w_i^2$. Then for every index $i$ the
[contrast variance](contrast-var.md) $\lambda_i(\hat\theta) = \hat\sigma_g^2 d_i + \hat\sigma_e^2$
is $m_a$ if $d_i = a$ and $m_b$ if $d_i = b$. The $d_i$ may take other values too.
