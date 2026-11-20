# Cox score vector

For subjects with observed times $T_i$, event indicators $\delta_i$ and covariate vectors
$x_i \in \mathbb{R}^p$, the Cox score vector is
$$U(\beta) = \sum_{i : \delta_i = 1} \bigl(x_i - \bar x_i(\beta)\bigr),$$
where $\bar x_i(\beta)$ is the weighted mean covariate vector over the risk set of subject $i$.
