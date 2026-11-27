# Posterior predictive at a new input

Let $m_0 \in \mathbb{R}$, let $s_0 > 0$ and
$\sigma^2 > 0$, and let $x \in \mathbb{R}^n$ and $x' \in \mathbb{R}$. Put the prior
$N(m_0, s_0)$ (mean $m_0$, variance $s_0$) on a scalar weight $w$, and let the responses be
independent given $w$ with $y_i \sim N(w x_i, \sigma^2)$. Then for Lebesgue-almost every
response vector $y \in \mathbb{R}^n$, integrating the law $N(w x', \sigma^2)$ of the response
at $x'$ against the posterior of $w$ given $y$ gives the Gaussian
$N(x' m, x'^2 v + \sigma^2)$, where
$m = (\sigma^2 m_0 + s_0 \sum_i x_i y_i) / (\sigma^2 + s_0 \sum_i x_i^2)$ and
$v = s_0 \sigma^2 / (\sigma^2 + s_0 \sum_i x_i^2)$ are the posterior mean and variance.
