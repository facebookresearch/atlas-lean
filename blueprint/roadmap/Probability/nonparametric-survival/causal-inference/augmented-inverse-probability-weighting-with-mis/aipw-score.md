# Aipw Score

Let $(\Omega, \mu)$ be a measure space and $X : \Omega \to \mathcal{X}$ a covariate. For a response event $R \subseteq \Omega$ on which the outcome $Y : \Omega \to \mathbb{R}$ is observed, a response propensity $\pi : \mathcal{X} \to \mathbb{R}$ and an outcome regression $m : \mathcal{X} \to \mathbb{R}$, the AIPW score for the mean of $Y$ is

$$\psi(\omega) = m(X(\omega)) + \mathbf{1}_R(\omega) \, \frac{Y(\omega) - m(X(\omega))}{\pi(X(\omega))}.$$

With the convention $a / 0 = 0$, on a stratum where $\pi(x) = 0$ the score is $m(X)$: the residual term is dropped.
