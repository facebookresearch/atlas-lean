# MAR is mean MAR for all transforms of the outcome

Let $\Omega$ be a standard Borel space, $\mu$ a finite measure on it, $R \subseteq \Omega$ a measurable response event, $X : \Omega \to \mathcal X$ a measurable covariate and $Y : \Omega \to \mathcal Y$ a measurable outcome, with $\mathcal X, \mathcal Y$ measurable spaces. Then the outcome is missing at random, meaning $\mathbf 1_R$ is conditionally independent of $Y$ given $\sigma(X)$ under $\mu$, if and only if for every measurable $g : \mathcal Y \to \mathbb R$ with $g(Y)$ integrable,

$$\mathbb E_\mu[\mathbf 1_R\, g(Y) \mid \sigma(X)] = \mathbb E_\mu[\mathbf 1_R \mid \sigma(X)]\, \mathbb E_\mu[g(Y) \mid \sigma(X)] \quad \mu\text{-a.e.}$$
