# Score vector with one covariate

For one covariate ($p = 1$), with covariate values $z_i$, the Cox score vector at $b$ has the scalar Cox
score $\sum_{i : \delta_i = 1} (z_i - \bar z_i(b))$ as its single component, where
$$\bar z_i(b) = \frac{\sum_{l \in R(T_i)} z_l \, e^{b z_l}}{\sum_{l \in R(T_i)} e^{b z_l}}$$
is the weighted mean of the covariate over the risk set $R(T_i) = \{l : T_l \ge T_i\}$ of subject $i$, with
weights $e^{b z_l}$.
