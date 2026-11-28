# The AIPW score with the true propensity integrates to the treatment-effect integral

Let $\mu$ be a finite measure on $\Omega_1$, $T \subseteq \Omega_1$ a measurable treatment event, $X : \Omega_1 \to \mathcal X$ a measurable covariate, and $Y, Y_0, Y_1 : \Omega_1 \to \mathbb R$ with $Y_0, Y_1$ integrable. Write $\mathbb E[\,\cdot \mid X]$ for conditional expectation given $\sigma(X)$. Assume

- consistency: $Y = \mathbf 1_T Y_1 + \mathbf 1_{T^c} Y_0$ $\mu$-a.e.;
- mean exchangeability: $\mathbb E[\mathbf 1_T Y_1 \mid X] = \mathbb E[\mathbf 1_T \mid X]\,\mathbb E[Y_1 \mid X]$ and $\mathbb E[\mathbf 1_{T^c} Y_0 \mid X] = (1 - \mathbb E[\mathbf 1_T \mid X])\,\mathbb E[Y_0 \mid X]$ a.e.

Let $e, m_0, m_1 : \mathcal X \to \mathbb R$ be measurable with $m_0(X)$ and $m_1(X)$ integrable, and suppose there is $\varepsilon > 0$ with $\varepsilon \le e(X) \le 1 - \varepsilon$ a.e., and that the propensity is correct: $e(X) = \mathbb E[\mathbf 1_T \mid X]$ a.e. Then the AIPW score

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

satisfies

$$\int \psi \, d\mu = \int (Y_1 - Y_0) \, d\mu.$$

When $\mu$ is a probability measure, this says that the score is unbiased for the average treatment effect.
