# Ipw Mean congr

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $Y : \Omega \to \mathbb R$ an outcome observed only on $R$. Let $X : \Omega \to \beta$ be a covariate and $\pi(x) = \mu(R \cap \{X = x\}) / \mu(X = x)$ (with $\pi(x) = 0$ when $\mu(X = x) = 0$). If $Y' : \Omega \to \mathbb R$ agrees with $Y$ on $R$, then the inverse-response-weighted means agree:

$$\int \mathbf 1_R\, \frac{Y}{\pi(X)} \, d\mu = \int \mathbf 1_R\, \frac{Y'}{\pi(X)} \, d\mu.$$
