# Certified thermal endpoint is the tenth Euler iterate

Let $C > 0$, $G > 0$, real $T_{\mathrm{amb}}$ and $\Delta$, $\tau = C/G$, and let $S(T) = T + (\tau/10)\,Q(T)/C$ with $Q(T) = -G(T - T_{\mathrm{amb}})$ be the explicit Euler step of size $\tau/10$. A list $y$ of rationals is accepted by the thermal trace checker when it has exactly eleven entries $y_0, \dots, y_{10}$, $y_0 = 1$, and $y_{j+1} = \tfrac{9}{10}\, y_j$ for $j = 0, \dots, 9$. If $y$ is accepted, then

$$T_{\mathrm{amb}} + \Delta\, y_{10} = S^{10}(T_{\mathrm{amb}} + \Delta).$$
