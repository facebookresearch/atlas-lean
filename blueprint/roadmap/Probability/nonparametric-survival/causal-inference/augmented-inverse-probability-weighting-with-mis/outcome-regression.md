# Outcome Regression

Let $(\Omega, \mu)$ be a measure space and $X : \Omega \to \mathcal{X}$ a covariate. For an outcome $Y : \Omega \to \mathbb{R}$ and a covariate value $x \in \mathcal{X}$, the full-data outcome regression is

$$m_Y(x) = \frac{\int_{\{X = x\}} Y \, d\mu}{\mu(X = x)},$$

the conditional mean $\mathbb{E}[Y \mid X = x]$ for a discrete covariate. By the convention $a / 0 = 0$ it equals $0$ when $\mu(X = x) = 0$.
