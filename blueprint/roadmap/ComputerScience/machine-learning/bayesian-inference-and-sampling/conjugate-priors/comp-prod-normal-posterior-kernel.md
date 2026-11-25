# Disintegration of the Normal–Normal joint law

Let $m_0 \in \mathbb{R}$ and $v_0, v > 0$,
and write $N(\mu, s)$ for the Gaussian law with mean $\mu$ and variance $s$. Let $\pi = N(m_0, v_0)$
be the prior on the parameter $\theta$, let $K$ be the Gaussian likelihood with noise variance $v$,
so that $K(\theta) = N(\theta, v)$, and let $Q$ be the normal posterior kernel,
$Q(x) = N(\mu(x), s)$ with $\mu(x) = (v m_0 + v_0 x)/(v_0 + v)$ and $s = v_0 v/(v_0 + v)$. For a
measure $\rho$ and a kernel $L$, write $L \circ \rho = \int L(y)\,d\rho(y)$ and $\rho \otimes L$ for
the law of $(y, z)$ when $y \sim \rho$ and $z \sim L(y)$. Then $(K \circ \pi) \otimes Q$ is the
image of $\pi \otimes K$ under $(\theta, x) \mapsto (x, \theta)$: the joint law of $(x, \theta)$ is
the marginal law $K \circ \pi$ of $x$ followed by the posterior kernel.
