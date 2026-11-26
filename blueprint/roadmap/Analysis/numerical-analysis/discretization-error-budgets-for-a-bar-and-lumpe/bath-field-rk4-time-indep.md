# RK4 step on the bath field does not depend on the start time

Let $C$, $G$, $T_{\mathrm{amb}}$, $t$, $T$, $\Delta t$ be real and $Q(T) = -G(T - T_{\mathrm{amb}})$. Write $\Phi_{\Delta t}(t, T)$ for one step of size $\Delta t$ of the classical fourth-order Runge–Kutta method (tableau $a_{21} = a_{32} = \tfrac12$, $a_{43} = 1$, other $a_{ij} = 0$, weights $(\tfrac16, \tfrac13, \tfrac13, \tfrac16)$) applied to $T' = f(t, T) = Q(T)/C$ from time $t$. Then

$$\Phi_{\Delta t}(t, T) = \Phi_{\Delta t}(0, T).$$

Real division by zero is $0$, so for $C = 0$ the field is $0$ and the step is the identity; the statement holds for every real $C$.
