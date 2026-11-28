# Full-data outcome regression

Let $(\Omega, \mu)$ be a measure space and $X : \Omega \to \mathcal{X}$ a covariate. For an outcome $Y : \Omega \to \mathbb{R}$ and a covariate value $x \in \mathcal{X}$, the full-data outcome regression is

$$m_Y(x) = \frac{\int_{\{X = x\}} Y \, d\mu}{\mu(X = x)},$$

with $a / 0 = 0$, the mass $\mu(X = x)$ read as a real number ($0$ when infinite) and the integral $0$ when the integrand is not integrable; so it equals $0$ when $\mu(X = x)$ is $0$ or infinite. When $\{X = x\}$ is measurable with positive finite mass and $Y$ is integrable on it, it is the conditional mean $\mathbb{E}[Y \mid X = x]$; an infinite-mass fibre does not carry a conditional probability law.
