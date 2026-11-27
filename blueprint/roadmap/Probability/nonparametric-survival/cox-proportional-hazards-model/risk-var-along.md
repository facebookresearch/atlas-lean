# Weighted variance along a direction over a risk set

For a direction $u \in \mathbb{R}^p$, the weighted variance of the linear covariate $\langle x, u \rangle$
over the risk set of subject $i$ is

$$V_i(\beta; u) = \frac{\sum_{l \in R(T_i)} \langle x_l, u \rangle^2 e^{\langle \beta, x_l \rangle}}{\sum_{l \in R(T_i)} e^{\langle \beta, x_l \rangle}} - \langle \bar x_i(\beta), u \rangle^2,$$

with weights $e^{\langle \beta, x_l \rangle}$.
