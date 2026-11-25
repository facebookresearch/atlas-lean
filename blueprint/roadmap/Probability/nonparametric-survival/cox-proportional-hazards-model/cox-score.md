# Cox score for a scalar covariate

For observed times $T_i$, event indicators $\delta_i \in \{0, 1\}$, a scalar covariate $z_i$ and $b \in \mathbb{R}$, the Cox score is

$$U(b) = \sum_{i : \delta_i = 1} \big(z_i - \bar z_i(b)\big),$$

with $\bar z_i(b)$ the [weighted mean over the risk set](risk-mean.md).
