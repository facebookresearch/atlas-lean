# Weighted mean of a covariate over a risk set

For observed times $T_l$, a scalar covariate $z_l \in \mathbb{R}$, $b \in \mathbb{R}$ and a subject $i$, the $e^{bz}$-weighted mean of $z$ over the [risk set](risk-set.md) of $i$ is

$$\bar z_i(b) = \frac{\sum_{l \in R(T_i)} z_l\, e^{b z_l}}{\sum_{l \in R(T_i)} e^{b z_l}}.$$
