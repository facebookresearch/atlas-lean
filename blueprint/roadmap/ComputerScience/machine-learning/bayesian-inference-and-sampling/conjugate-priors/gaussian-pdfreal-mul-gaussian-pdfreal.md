# Completing the square

Let $m_0, \theta, x \in \mathbb{R}$ and $v_0, v > 0$, and write
$\varphi_{\mu, s}(y) = (2 \pi s)^{-1/2} \exp(-(y - \mu)^2 / (2 s))$ for the density of the Gaussian
with mean $\mu$ and variance $s$. With $\mu(x) = (v m_0 + v_0 x)/(v_0 + v)$ and
$s = v_0 v/(v_0 + v)$,

$$
\varphi_{m_0, v_0}(\theta)\,\varphi_{\theta, v}(x) =
\varphi_{m_0, v_0 + v}(x)\,\varphi_{\mu(x), s}(\theta):
$$

the prior density at $\theta$ times the likelihood of $x$ is the marginal density of $x$ times the
posterior density at $\theta$.
