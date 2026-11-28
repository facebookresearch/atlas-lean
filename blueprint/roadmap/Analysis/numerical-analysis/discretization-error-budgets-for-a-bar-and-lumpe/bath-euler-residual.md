# Residual of a computed sequence in the bath Euler recurrence

For real $C$, $G$, $T_{\mathrm{amb}}$, $\tau = C/G$, $Q(T) = -G(T - T_{\mathrm{amb}})$ and a computed temperature sequence $Y : \mathbb{N} \to \mathbb{R}$, the residual of step $j$ is

$$\eta_j = Y_{j+1} - \left(Y_j + \frac{(\tau/10)\, Q(Y_j)}{C}\right),$$

the amount by which the computed step misses one exact Euler step of size $\tau/10$.

Real division by zero is $0$: $\tau = C/G$ is $0$ when $G = 0$, and $Q(T)/C$ is $0$ when $C = 0$, so then the Euler step is the identity.
