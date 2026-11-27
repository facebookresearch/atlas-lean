# RK4 recurrence for bath cooling at step $\tau/10$

Let $C, G > 0$, let $T_{\mathrm{amb}}, \Delta \in \mathbb{R}$, write $Q(T) = -G\,(T - T_{\mathrm{amb}})$ for the power delivered by the bath and $\tau = C/G$ for the thermal time constant. Let $f(t, T) = Q(T)/C$, and let $\Phi(t, T)$ denote one step of size $\tau/10$ from $(t, T)$ of the classical fourth-order Runge–Kutta method applied to $f$. If $X : \mathbb{N} \to \mathbb{R}$ satisfies $X_0 = T_{\mathrm{amb}} + \Delta$ and

$$X_{j+1} = \Phi\!\left(j\,\tfrac{\tau}{10},\, X_j\right) \quad \text{for all } j,$$

then for every $j \in \mathbb{N}$,

$$X_j = T_{\mathrm{amb}} + \Delta \left(\tfrac{72387}{80000}\right)^j.$$
