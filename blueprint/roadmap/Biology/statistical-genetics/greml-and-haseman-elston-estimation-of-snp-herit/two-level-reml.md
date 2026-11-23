# Closed-form REML estimate for a two-level spectrum

For a finite index set $r$, real vectors $d, w \in \mathbb{R}^r$ and reals $a$ and $b$, let $m_a$
and $m_b$ be the [class means](group-mean.md) of $w_i^2$ over the indices with $d_i = a$ and with
$d_i = b$. The closed-form estimate is $\hat\theta = (\hat\sigma_g^2, \hat\sigma_e^2)$ with

$$\hat\sigma_g^2 = \frac{m_a - m_b}{a - b}, \qquad \hat\sigma_e^2 = \frac{a m_b - b m_a}{a - b}.$$

It is defined for all inputs: with the convention $x / 0 = 0$ both components are $0$ when
$a = b$, an empty class has mean $0$, and indices with $d_i \notin \{a, b\}$ do not enter. The
intended domain is a spectrum taking only the two values $a \ne b$. There, when both class means
are positive, $\hat\theta$ is the unique maximizer of the [spectral REML criterion](spectral-log-lik.md)
over the parameters with positive contrast variances
([spectral maximizer](is-max-on-spectral-log-lik-two-level-rem.md)), and so of the GREML restricted
log-likelihood when $w = By$ for an orthonormal contrast $B$ that diagonalizes the relationship
matrix ([closed-form maximizer](is-max-on-reml-log-lik-two-level-reml.md)). It is not constrained to
nonnegative variances: $a = 3/2$, $b = 1/2$, $m_a = 1$ and $m_b = 2$ give $\hat\sigma_g^2 = -1$.
