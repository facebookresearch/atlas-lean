# Excess after ten RK4 steps of bath cooling

Let $C > 0$, $G > 0$, real $T_{\mathrm{amb}}$ and $\Delta$, and put $\tau = C/G$ and $Q(T) = -G(T - T_{\mathrm{amb}})$. Write $\Phi_{\Delta t}(t, T)$ for one step of size $\Delta t$ of the classical fourth-order Runge–Kutta method (tableau $a_{21} = a_{32} = \tfrac12$, $a_{43} = 1$, other $a_{ij} = 0$, weights $(\tfrac16, \tfrac13, \tfrac13, \tfrac16)$) applied to $T' = f(t, T) = Q(T)/C$ from time $t$. Let $(X_j)$ be a real sequence with $X_0 = T_{\mathrm{amb}} + \Delta$ and $X_{j+1} = \Phi_{\tau/10}(j\tau/10,\, X_j)$ for every $j$. Then

$$X_{10} - T_{\mathrm{amb}} = \Delta \left(\frac{72387}{80000}\right)^{10}.$$
