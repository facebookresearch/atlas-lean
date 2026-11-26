# The common-covariance statistic in dimension one

In dimension one, take means $m_1, m_0 \in \mathbb{R}$, the $1 \times 1$ covariance matrix $R = [v]$ with $v \in \mathbb{R}$, and $y \in \mathbb{R}$. The common-covariance log-likelihood ratio statistic $(s_1 - s_0)^{\mathsf T} R^{-1} y - \tfrac12 (s_1^{\mathsf T} R^{-1} s_1 - s_0^{\mathsf T} R^{-1} s_0)$ with $s_i = (m_i)$ equals

$$\frac{(m_1 - m_0)\, y}{v} - \frac{m_1^2 - m_0^2}{2v},$$

with the conventions $x / 0 = 0$ and $[0]^{-1} = [0]$ when $v = 0$.

This is an algebraic identity for every real $v$. For $v > 0$ the right side is the log-likelihood ratio of the Gaussian laws $\mathcal N(m_1, v)$ and $\mathcal N(m_0, v)$ at $y$. For $v < 0$ there is no Gaussian law with variance $v$, and for $v = 0$ with $m_1 \ne m_0$ the two laws are mutually singular point masses, so no finite log-likelihood ratio exists, although the expression is $0$.
