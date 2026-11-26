# Death counting process of the two-coin censoring model

On the sample space $\Omega_0 = \{\mathrm{true}, \mathrm{false}\}^2$ of the two-coin censoring model, with points $\omega = (c, d)$ (censoring coin $c$, death coin $d$), the death counting process $N : \mathbb N \to \Omega_0 \to \mathbb R$ is

$$N_n(c, d) = \begin{cases} 1, & n \ge 2,\ c = \mathrm{false} \text{ and } d = \mathrm{true}, \\ 0, & \text{otherwise}. \end{cases}$$

The subject is counted as dead from step $2$ on exactly when it was not censored and the death coin came up.
