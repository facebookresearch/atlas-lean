# Normal–Normal posterior predictive

Let $m_0 \in \mathbb{R}$ and $v_0, v > 0$, and write
$N(\mu, s)$ for the Gaussian law with mean $\mu$ and variance $s$. Take the prior $N(m_0, v_0)$ on
the parameter $\theta$ and the Gaussian likelihood $\theta \mapsto N(\theta, v)$, and let
$\mu(x) = (v m_0 + v_0 x)/(v_0 + v)$ and $s = v_0 v/(v_0 + v)$. For Lebesgue-almost every
observation $x$, a new observation drawn from the likelihood, with $\theta$ distributed according
to the posterior given $x$, has law $N(\mu(x), s + v)$.
