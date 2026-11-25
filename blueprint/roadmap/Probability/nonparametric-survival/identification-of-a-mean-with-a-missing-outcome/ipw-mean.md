# Ipw Mean

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $Y : \Omega \to \mathbb R$ an outcome observed only on $R$. Let $X : \Omega \to \beta$ be an always-observed covariate. The inverse-response-weighted mean (Horvitz & Thompson 1952) is

$$\int \mathbf 1_R(\omega)\, \frac{Y(\omega)}{\pi(X(\omega))} \, d\mu(\omega), \qquad \pi(x) = \frac{\mu(R \cap \{X = x\})}{\mu(X = x)},$$

where $\pi$ is the response probability given $X = x$, taken to be $0$ when $\mu(X = x) = 0$, and $y / 0 = 0$. It depends on $Y$ only through its values on $R$, so it is an observed-data estimand.
