# Control residual

Let $(\Omega, \mu)$ be a probability space, $X : \Omega \to \mathcal{X}$ a covariate with values in a measurable space, $T \subseteq \Omega$ the treatment event, $Y$ the observed outcome, $Y_0, Y_1$ the potential outcomes, and $e, m_0, m_1, s_0, s_1 : \mathcal{X} \to \mathbb{R}$. Assume the setting of Hahn's variance formula:

- $T$ is measurable and $X$ is measurable; write $\mathbb{E}[\,\cdot \mid X]$ for conditional expectation given $\sigma(X)$;
- consistency: $Y = Y_1$ on $T$ and $Y = Y_0$ on $T^c$, at every point;
- $Y_0, Y_1 \in L^2(\mu)$;
- $e, m_0, m_1 : \mathcal{X} \to \mathbb{R}$ are measurable, and strong overlap holds: for some $\varepsilon > 0$, $\varepsilon \le e(x) \le 1 - \varepsilon$ for every $x \in \mathcal{X}$;
- $e$ is the true propensity, $\mathbb{E}[\mathbf{1}_T \mid X] = e(X)$; $m_a$ is the true outcome regression, $\mathbb{E}[Y_a \mid X] = m_a(X)$; and $s_a$ is the conditional variance, $\mathbb{E}[(Y_a - m_a(X))^2 \mid X] = s_a(X)$, for $a = 0, 1$, all $\mu$-a.e.;
- mean exchangeability: $\mathbb{E}[\mathbf{1}_T Y_1 \mid X] = \mathbb{E}[\mathbf{1}_T \mid X]\, \mathbb{E}[Y_1 \mid X]$ and $\mathbb{E}[\mathbf{1}_{T^c} Y_0 \mid X] = \mathbb{E}[\mathbf{1}_{T^c} \mid X]\, \mathbb{E}[Y_0 \mid X]$ a.e.;
- second-moment exchangeability: $\mathbb{E}[\mathbf{1}_T (Y_1 - m_1(X))^2 \mid X] = \mathbb{E}[\mathbf{1}_T \mid X]\, \mathbb{E}[(Y_1 - m_1(X))^2 \mid X]$ and $\mathbb{E}[\mathbf{1}_{T^c} (Y_0 - m_0(X))^2 \mid X] = \mathbb{E}[\mathbf{1}_{T^c} \mid X]\, \mathbb{E}[(Y_0 - m_0(X))^2 \mid X]$ a.e.

Let $\psi = m_1(X) - m_0(X) + \mathbf{1}_T (Y - m_1(X))/e(X) - \mathbf{1}_{T^c} (Y - m_0(X))/(1 - e(X))$ be the AIPW score at these nuisances. Then the control weighted residual $B_0 = \mathbf{1}_{T^c} (Y - m_0(X))/(1 - e(X))$ satisfies: $B_0 \in L^2(\mu)$, $s_0(X)/(1 - e(X))$ is integrable,

$$\int_\Omega B_0^2 \, d\mu = \int_\Omega \frac{s_0(X)}{1 - e(X)}\, d\mu, \qquad \mathbb{E}[B_0 \mid X] = 0 \ \ \mu\text{-a.e.}$$
