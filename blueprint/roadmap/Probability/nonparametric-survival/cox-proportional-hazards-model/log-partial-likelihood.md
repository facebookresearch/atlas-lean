# Cox log partial likelihood

For observed times $T_i$, event indicators $\delta_i \in \{0, 1\}$ and covariates $x_i \in \mathbb{R}^p$, the log partial likelihood at $\beta \in \mathbb{R}^p$ is

$$\ell(\beta) = \sum_{i : \delta_i = 1} \Big(\langle \beta, x_i \rangle - \log \sum_{l \in R(T_i)} \exp\langle \beta, x_l \rangle\Big).$$
