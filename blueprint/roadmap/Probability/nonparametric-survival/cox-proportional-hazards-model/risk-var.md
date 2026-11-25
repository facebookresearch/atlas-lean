# Weighted variance of a covariate over a risk set

For observed times $T_l$, a scalar covariate $z_l \in \mathbb{R}$, $b \in \mathbb{R}$ and a subject $i$, the $e^{bz}$-weighted variance of $z$ over the [risk set](risk-set.md) of $i$ is

$$V_i(b) = \frac{\sum_{l \in R(T_i)} z_l^2\, e^{b z_l}}{\sum_{l \in R(T_i)} e^{b z_l}} - \bar z_i(b)^2,$$

with $\bar z_i(b)$ the [weighted mean](risk-mean.md).
