# Correct outcome regression, control arm

Let $\mu$ be a finite measure on $\Omega$, $X : \Omega \to \mathcal{X}$ measurable, and write $\mathbb{E}[\,\cdot \mid X]$ for conditional expectation given $\sigma(X)$. Let $T \subseteq \Omega$ be measurable and $Y, Y_0, Y_1 : \Omega \to \mathbb{R}$ with consistency at every point, $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$. Assume $Y_0$ is integrable and mean exchangeability $\mathbb{E}[\mathbf{1}_{T^c} Y_0 \mid X] = \mathbb{E}[\mathbf{1}_{T^c} \mid X]\, \mathbb{E}[Y_0 \mid X]$ holds $\mu$-a.e. Let $e, m_0 : \mathcal{X} \to \mathbb{R}$ be measurable with $e(x) \le 1 - \varepsilon$ for every $x$ and some $\varepsilon > 0$. If the outcome regression is correct, $\mathbb{E}[Y_0 \mid X] = m_0(X)$ $\mu$-a.e., then

$$\mathbb{E}\left[\mathbf{1}_{T^c} \, \frac{Y - m_0(X)}{1 - e(X)} \;\middle|\; X\right] = 0 \quad \mu\text{-a.e.}$$

The propensity $e$ need not be correct.
