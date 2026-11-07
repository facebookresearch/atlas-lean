# Prior times likelihood factors as evidence times posterior

Let $m_0 \in \mathbb{R}$,
let $s_0, \sigma^2 \ge 0$ be nonzero, let $x, y \in \mathbb{R}^n$ and let $w \in \mathbb{R}$.
Write $\varphi(t; \mu, \tau)$ for the Gaussian density with mean $\mu$ and variance $\tau$ at $t$,
$L(y \mid w) = \prod_i \varphi(y_i; w x_i, \sigma^2)$ for the likelihood density, $m$ and $v$ for
the posterior mean and variance of the weight, and $Z(y)$ for the evidence density. Then
$\varphi(w; m_0, s_0) \, L(y \mid w) = Z(y) \, \varphi(w; m, v)$.
