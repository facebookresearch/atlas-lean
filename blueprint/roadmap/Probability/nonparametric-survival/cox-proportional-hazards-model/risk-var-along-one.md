# Directional variance with one covariate

For one covariate ($p = 1$) with values $z_l$ and the unit direction $u = 1$, the weighted variance along
$u$ at $b$ is the scalar weighted variance

$$\frac{\sum_{l \in R(T_i)} z_l^2 \, e^{b z_l}}{\sum_{l \in R(T_i)} e^{b z_l}} - \bar z_i(b)^2,$$

where

$$\bar z_i(b) = \frac{\sum_{l \in R(T_i)} z_l \, e^{b z_l}}{\sum_{l \in R(T_i)} e^{b z_l}}$$

is the weighted mean of the covariate over the risk set $R(T_i) = \{l : T_l \ge T_i\}$ of subject $i$, with
weights $e^{b z_l}$.
