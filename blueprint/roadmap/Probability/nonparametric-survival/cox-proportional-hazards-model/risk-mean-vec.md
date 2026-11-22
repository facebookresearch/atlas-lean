# Weighted mean covariate vector over a risk set

For subjects $l = 1, \dots, n$ with observed times $T_l$ and covariate vectors $x_l \in \mathbb{R}^p$, the
weighted mean covariate vector over the risk set $R(T_i) = \{l : T_l \ge T_i\}$ of subject $i$ is

$$\bar x_i(\beta) = \frac{\sum_{l \in R(T_i)} e^{\langle \beta, x_l \rangle} x_l}{\sum_{l \in R(T_i)} e^{\langle \beta, x_l \rangle}}.$$
