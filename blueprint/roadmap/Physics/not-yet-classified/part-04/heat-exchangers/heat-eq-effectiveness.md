# Heat duty of a parallel-flow exchanger

Let $C_h, C_c > 0$ be the stream capacity rates, $L > 0$ the length, $UA$ the overall conductance and $T_{h,i}, T_{c,i}$ the inlet temperatures. Let $C_{\min} = \min(C_h, C_c)$, $C_{\max} = \max(C_h, C_c)$, $C_r = C_{\min}/C_{\max}$, $\mathrm{NTU} = UA / C_{\min}$ and

$$\varepsilon_p(\mathrm{NTU}, C_r) = \frac{1 - e^{-\mathrm{NTU}(1 + C_r)}}{1 + C_r}.$$

If $(T_h, T_c)$ is a parallel-flow solution on $[0, L]$ with conductance per unit length $K = UA/L$ and inlets $T_{h,i}, T_{c,i}$ at $x = 0$, then

$$C_h\big(T_{h,i} - T_h(L)\big) = \varepsilon_p(\mathrm{NTU}, C_r)\,C_{\min}\,(T_{h,i} - T_{c,i}) = C_c\big(T_c(L) - T_{c,i}\big).$$
