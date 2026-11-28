# At-risk process of the two-coin censoring model

On the sample space $\Omega_0 = \{\mathrm{true}, \mathrm{false}\}^2$ of the two-coin censoring model, with points $\omega = (c, d)$ (censoring coin $c$, death coin $d$), the at-risk process $Y : \mathbb N \to \Omega_0 \to \mathbb R$ is

$$Y_n(c, d) = \begin{cases} 1, & n = 1, \text{ or } n = 2 \text{ and } c = \mathrm{false}, \\ 0, & \text{otherwise}. \end{cases}$$

The subject is at risk at step $1$, at step $2$ only if it was not censored at time $1$, and at no other step, step $0$ included.
