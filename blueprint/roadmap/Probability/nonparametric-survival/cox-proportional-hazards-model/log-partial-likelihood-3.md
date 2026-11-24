# Log partial likelihood of a scalar covariate

For observed times $T_i$, event indicators $\delta_i$ and a scalar covariate $z_i \in \mathbb{R}$, the [log partial likelihood](log-partial-likelihood.md) with $p = 1$ as a function of $b \in \mathbb{R}$:

$$\ell_1(b) = \sum_{i : \delta_i = 1} \Big(b z_i - \log \sum_{l \in R(T_i)} e^{b z_l}\Big).$$
