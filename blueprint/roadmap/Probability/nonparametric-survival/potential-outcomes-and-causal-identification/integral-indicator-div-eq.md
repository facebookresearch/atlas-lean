# Integral indicator div eq

Let $\mu$ be a measure on $\Omega$, $\mathcal X$ a finite measurable space with measurable singletons, $S \subseteq \Omega$ measurable, $X : \Omega \to \mathcal X$ measurable, $Y : \Omega \to \mathbb R$ integrable, and $p : \mathcal X \to \mathbb R$. Suppose $p(x) \ne 0$ whenever $\mu(X = x) \ne 0$, and for every $x \in \mathcal X$

$$\int_{S \cap \{X = x\}} Y \, d\mu = p(x) \int_{\{X = x\}} Y \, d\mu.$$

Then $\mathbf 1_S\, Y / p(X)$ is integrable and

$$\int \mathbf 1_S(\omega)\, \frac{Y(\omega)}{p(X(\omega))} \, d\mu(\omega) = \int Y \, d\mu,$$

with the convention $y / 0 = 0$.
