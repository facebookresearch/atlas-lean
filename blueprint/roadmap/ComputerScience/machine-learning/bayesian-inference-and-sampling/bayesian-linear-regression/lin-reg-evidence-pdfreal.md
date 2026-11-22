# The evidence density of Bayesian linear regression

For $m_0 \in \mathbb{R}$,
$s_0, \sigma^2 \ge 0$ and $x, y \in \mathbb{R}^n$, let $m$ and $v$ be the posterior mean and
variance of the weight, write $\varphi(t; \mu, \tau) = (2\pi\tau)^{-1/2} e^{-(t - \mu)^2 / (2\tau)}$
for the Gaussian density with mean $\mu$ and variance $\tau$ at $t$ (read as $0$ when $\tau = 0$),
and let $L(y \mid w) = \prod_i \varphi(y_i; w x_i, \sigma^2)$ be the likelihood density. The
evidence density at $y$ is

$$Z(y) = \frac{\varphi(m; m_0, s_0) \, L(y \mid m)}{\varphi(m; m, v)},$$

prior density times likelihood divided by the posterior density, all at the posterior mean (a
quotient by $0$ is read as $0$).

For $s_0 \ne 0$ and $\sigma^2 \ne 0$ the ratio does not depend on the point where it is evaluated,
and $Z$ is the Lebesgue density of the marginal law of the data. It is not a density of the
evidence in the degenerate cases.
