# The inverse-response-weighted integral depends only on respondents

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $Y : \Omega \to \mathbb R$ an outcome observed only on $R$. Let $X : \Omega \to \beta$ be a covariate and $\pi(x) = \mu(R \cap \{X = x\}) / \mu(X = x)$ (with $y / 0 = 0$, each measure read as a real number, $0$ when infinite, so $\pi(x) = 0$ when $\mu(X = x)$ is $0$ or infinite). If $Y' : \Omega \to \mathbb R$ agrees with $Y$ on $R$, then the inverse-response-weighted integrals agree:

$$\int \mathbf 1_R\, \frac{Y}{\pi(X)} \, d\mu = \int \mathbf 1_R\, \frac{Y'}{\pi(X)} \, d\mu.$$

The integrals are Bochner integrals, $0$ when the integrand is not integrable. For a probability measure $\mu$ they are the inverse-response-weighted means.
