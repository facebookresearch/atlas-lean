# Counterflow effectiveness

Let $C_h, C_c > 0$ be the hot and cold capacity rates, $UA \ge 0$ the overall conductance and $L > 0$ the exchanger length. Let $(T_h, T_c)$ solve the counterflow equations on $[0, L]$ with conductance per unit length $UA/L$, hot inlet $T_h(0) = T_{hi}$ and cold inlet $T_c(L) = T_{ci}$. With $C_{\min} = \min(C_h, C_c)$, $C_r = C_{\min}/\max(C_h, C_c)$, $\mathrm{NTU} = UA/C_{\min}$ and the counterflow effectiveness

$$\varepsilon_c = \begin{cases} \dfrac{\mathrm{NTU}}{1 + \mathrm{NTU}} & C_r = 1,\\[1ex] \dfrac{1 - e^{-\mathrm{NTU}(1 - C_r)}}{1 - C_r e^{-\mathrm{NTU}(1 - C_r)}} & C_r \ne 1,\end{cases}$$

both

$$C_h\,(T_{hi} - T_h(L)) = \varepsilon_c\, C_{\min}\,(T_{hi} - T_{ci}) \quad\text{and}\quad C_c\,(T_c(0) - T_{ci}) = \varepsilon_c\, C_{\min}\,(T_{hi} - T_{ci}).$$
