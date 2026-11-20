# Derivative of the log partial likelihood in several covariates

The Cox log partial likelihood
$$\ell(\beta) = \sum_{i : \delta_i = 1} \Bigl(\langle \beta, x_i \rangle - \log \sum_{l \in R(T_i)} e^{\langle \beta, x_l \rangle}\Bigr)$$
is differentiable on $\mathbb{R}^p$, and its derivative at $\beta$ is the linear map
$v \mapsto \langle v, U(\beta) \rangle$, where $U$ is the Cox score vector.
