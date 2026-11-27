# Inverse-response-weighted integral

Let $\mu$ be a measure on a measurable space $\Omega$, $R \subseteq \Omega$ the response event and $Y : \Omega \to \mathbb R$ an outcome observed only on $R$. Let $X : \Omega \to \beta$ be an always-observed covariate. The inverse-response-weighted integral (Horvitz & Thompson 1952) is

$$\int \mathbf 1_R(\omega)\, \frac{Y(\omega)}{\pi(X(\omega))} \, d\mu(\omega), \qquad \pi(x) = \frac{\mu(R \cap \{X = x\})}{\mu(X = x)},$$

where $\pi$ is the exact-fibre response ratio and $y / 0 = 0$, so $\pi(x) = 0$ when $\mu(X = x) = 0$. Each $\mu(\cdot)$ in $\pi$ is the real number $\mu(\cdot)$ when it is finite and $0$ when it is infinite (an outer measure for a non-measurable fibre), and the integral is a Bochner integral, $0$ when the integrand is not integrable. It depends on $Y$ only through its values on $R$, so it is an observed-data estimand. When $\mu$ is a probability measure it is the inverse-response-weighted mean $\mathbb E[\mathbf 1_R\, Y / \pi(X)]$. For other measures it is a weighted integral, not a mean: $\pi$ does not change when $\mu$ is multiplied by a positive constant, so doubling $\mu$ doubles the value (on a one-point space with $\mu = 2\delta$, every unit responding and $Y = 1$, the integral is $2$).

When $\{X = x\}$ is measurable with positive finite mass and the response is measurable on that fibre, that is $R \cap \{X = x\}$ is measurable (in particular when $R$ is measurable), $\pi(x)$ is the probability of response given $X = x$. Without that, a response set and its complement can both have ratio $1$. It is not the conditional response probability in general: for a covariate whose law has no atoms every fibre has mass $0$, so $\pi$ is identically $0$, even when every unit responds.
