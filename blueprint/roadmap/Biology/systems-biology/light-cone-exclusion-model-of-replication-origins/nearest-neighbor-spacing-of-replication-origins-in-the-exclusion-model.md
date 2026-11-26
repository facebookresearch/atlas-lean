# Nearest-neighbor spacing of replication origins in the exclusion model

**Exclusion model.** Scatter a homogeneous Poisson point process of unit intensity on $\mathbb R \times \mathbb R_+$, read as (position on the chromosome, time). Each point is a potential origin firing; a fired origin sends two replication forks outward at unit speed, so its influence is its *forward light cone* $\{(x',t') : |x - x'| \le t' - t\}$. A point $(x,t)$ is *active* (a realized origin) if its *backward light cone* $\{(x',t') : |x - x'| \le t - t'\}$ contains no other Poisson point, that is, if no earlier potential origin has already replicated position $x$ by time $t$.

**Theorem 2.2 (spacing density).** Let $P(s)\,ds$ be the probability that, given an active point, the next active point along the chromosome lies at distance between $s$ and $s + ds$. Then

$$P(s) = \frac{1}{\rho_b}\Big[s\sqrt\pi\Big(1 - 2\,\mathrm{erf}(s) + \mathrm{erf}\big(\tfrac s2\big)\Big) - 2e^{-s^2} + 2e^{-s^2/4}\Big], \qquad s > 0,$$

where $\rho_b$ is the spatial density of active points.

**Lemma 2.3.** $\rho_b = \sqrt\pi/2$.

**Corollary 2.4 (local linear repulsion).** $P(s) = 2s + O(s^2)$ as $s \to 0$.

**Corollary 2.5 (Gaussian tail).** $P(s) = \dfrac{8}{\sqrt\pi\,s^2}e^{-s^2/4} + O\big(e^{-s^2/4}s^{-4}\big)$ as $s \to \infty$.

Compared with the exponential spacing $e^{-s}$ of independent points of the same density, active origins repel each other linearly at short distance and large gaps are far rarer, matching the qualitative pattern observed in yeast origin data.

## Expansion

An active point at $(0,t)$ requires its backward cone, a triangle of area $t^2$, to be empty, which has probability $e^{-t^2}$; integrating over $t$ gives the density $\int_0^\infty e^{-t^2}\,dt = \sqrt\pi/2$. Two active points at $(0,t_1)$ and $(s,t_2)$ with no active point between them require a space-time region built from their backward cones and the strip between them to be empty of Poisson points; its area is an explicit piecewise-quadratic function of $s$, $t_1$ and $t_2$. Integrating $e^{-\text{area}}$ over the two firing times gives the error-function expression. The small-$s$ and large-$s$ expansions of the resulting error-function expression give the linear repulsion and the $e^{-s^2/4}$ tail.

## Sources

- H. Day, N. C. Snaith, "Stochastic Models for Replication Origin Spacings in Eukaryotic DNA Replication" (2022), Section 2 (Definition 2.1, Theorem 2.2, Lemma 2.3, Corollaries 2.4 and 2.5), <https://doi.org/10.48550/arXiv.2209.09680>.
