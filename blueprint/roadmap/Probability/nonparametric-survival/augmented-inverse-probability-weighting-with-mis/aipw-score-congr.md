# Aipw Score congr

Let $(\Omega, \mu)$ be a measure space and $X : \Omega \to \mathcal{X}$ a covariate. Let $R \subseteq \Omega$, $\pi, m : \mathcal{X} \to \mathbb{R}$, and $Y, Y' : \Omega \to \mathbb{R}$ with $Y = Y'$ on $R$. Then the AIPW scores agree everywhere:

$$m(X) + \mathbf{1}_R \, \frac{Y - m(X)}{\pi(X)} = m(X) + \mathbf{1}_R \, \frac{Y' - m(X)}{\pi(X)}.$$

So the score depends on $Y$ only on the response event and is a statistic of the observed data.
