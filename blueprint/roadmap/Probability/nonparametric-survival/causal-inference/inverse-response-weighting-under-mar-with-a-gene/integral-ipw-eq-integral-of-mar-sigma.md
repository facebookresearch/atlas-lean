# Identification by inverse-response weighting under MAR, general covariate σ-algebra

Let $\mu$ be a probability measure on a measurable space $(\Omega, \mathcal F)$, $\mathcal G \subseteq \mathcal F$ a sub-σ-algebra (the always-observed covariate information), and $R \in \mathcal F$ the response event. Write $P(A \mid \mathcal G) = \mathbb E_\mu[\mathbf 1_A \mid \mathcal G]$. Let $Y : \Omega \to \mathbb R$ be measurable and integrable, and write $\pi = P(R \mid \mathcal G)$ for the response probability. Suppose $Y$ is missing at random given $\mathcal G$ in the set-wise form: for every measurable $S \subseteq \mathbb R$,

$$P(R \cap \{Y \in S\} \mid \mathcal G) = \pi\, P(Y \in S \mid \mathcal G) \quad \mu\text{-a.e.}$$

and strong positivity holds: there is $\varepsilon > 0$ with $\pi \ge \varepsilon$ $\mu$-a.e. Then the inverse-response-weighted mean equals the full-data mean:

$$\int \mathbf 1_R\, \frac{Y}{\pi} \, d\mu = \int Y \, d\mu,$$

with $y / 0 = 0$.
