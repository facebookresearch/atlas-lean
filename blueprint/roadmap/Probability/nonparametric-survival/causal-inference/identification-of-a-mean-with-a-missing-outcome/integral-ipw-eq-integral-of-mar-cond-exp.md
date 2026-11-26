# Identification by inverse-response weighting under MAR, general covariate

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal F)$, $\mathcal G \subseteq \mathcal F$ a sub-σ-algebra (the always-observed covariate information), $R \in \mathcal F$ the response event, and $Y : \Omega \to \mathbb R$ integrable. Let $\pi = \mathbb E_\mu[\mathbf 1_R \mid \mathcal G]$ be the response probability. Suppose the outcome is mean-missing-at-random,

$$\mathbb E_\mu[\mathbf 1_R Y \mid \mathcal G] = \pi\, \mathbb E_\mu[Y \mid \mathcal G] \quad \mu\text{-a.e.},$$

and strong positivity holds: there is $\varepsilon > 0$ with $\pi \ge \varepsilon$ $\mu$-a.e. Then

$$\int \mathbf 1_R\, \frac{Y}{\pi} \, d\mu = \int Y \, d\mu,$$

with $y / 0 = 0$.
