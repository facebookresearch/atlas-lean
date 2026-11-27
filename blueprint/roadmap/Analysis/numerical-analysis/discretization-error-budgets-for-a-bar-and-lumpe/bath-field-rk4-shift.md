# RK4 step on the bath field is a shifted linear-decay step

Let $C$, $G$, $T_{\mathrm{amb}}$, $t$, $T$, $\Delta t$ be real, $Q(T) = -G(T - T_{\mathrm{amb}})$ and $\tau = C/G$. Write $\Phi_{\Delta t}(t, T)$ for one step of size $\Delta t$ of the classical fourth-order Runge–Kutta method (tableau $a_{21} = a_{32} = \tfrac12$, $a_{43} = 1$, other $a_{ij} = 0$, weights $(\tfrac16, \tfrac13, \tfrac13, \tfrac16)$) applied to $T' = f(t, T) = Q(T)/C$ from time $t$. Let $\Psi_{\Delta t}(\theta)$ be one RK4 step of size $\Delta t$ from time $0$ for the linear decay $\theta' = (-1/\tau)\,\theta$. Then

$$\Phi_{\Delta t}(t, T) = T_{\mathrm{amb}} + \Psi_{\Delta t}(T - T_{\mathrm{amb}}).$$

Real division by zero is $0$: $Q(T)/C$ is $0$ when $C = 0$, and $\tau = C/G$ and $-1/\tau$ are $0$ when $G = 0$ or $C = 0$; the identity holds in all these cases.
