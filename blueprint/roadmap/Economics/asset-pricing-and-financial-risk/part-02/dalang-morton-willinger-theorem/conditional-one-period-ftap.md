# Conditional one-period fundamental theorem of asset pricing

Let $(\Omega, \mathcal F, \mathbb P)$ be a probability space, $\mathcal G \subseteq \mathcal F$ a sub-$\sigma$-field, and $\Delta S$ an $\mathcal F$-measurable random vector in $\mathbb R^d$, the one-period discounted price increments of $d$ assets. Say that there is *no arbitrage given $\mathcal G$* if every $\mathcal G$-measurable $\xi$ with values in $\mathbb R^d$ and $\xi \cdot \Delta S \ge 0$ almost surely satisfies $\xi \cdot \Delta S = 0$ almost surely. Then there is no arbitrage given $\mathcal G$ if and only if there is an $\mathcal F$-measurable random variable $Z$ with $0 < Z \le c$ for a constant $c$, $\mathbb E[Z \mid \mathcal G] = 1$, $\mathbb E[Z\, |\Delta S|] < \infty$ and

$$\mathbb E[Z\, \Delta S \mid \mathcal G] = 0 \quad \text{almost surely},$$

so that under $Q = Z \cdot \mathbb P$, an equivalent probability measure with bounded density, the increments have conditional mean zero given $\mathcal G$. No finiteness of $\Omega$ is assumed.

## Expansion

This page becomes ready once:

- the measurable-selection and closedness argument for the set of attainable conditional gains on a general probability space is stated (statement prerequisite)

## Sources

- R. C. Dalang, A. Morton and W. Willinger, "Equivalent martingale measures and no-arbitrage in stochastic securities market models", *Stochastics and Stochastic Reports* 29(2):185–201, 1990
- Y. M. Kabanov and C. Stricker, "A teachers' note on no-arbitrage criteria", *Séminaire de Probabilités XXXV*, Lecture Notes in Mathematics 1755, Springer, 2001
