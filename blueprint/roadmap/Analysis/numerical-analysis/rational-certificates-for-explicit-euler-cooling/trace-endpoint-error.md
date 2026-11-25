# Error bound for the certified thermal endpoint

Let $C > 0$, $G > 0$, real $T_{\mathrm{amb}}$ and $\Delta$, and $\tau = C/G$. A list $y$ of rationals is accepted by the thermal trace checker when it has exactly eleven entries $y_0, \dots, y_{10}$, $y_0 = 1$, and $y_{j+1} = \tfrac{9}{10}\, y_j$ for $j = 0, \dots, 9$. If $y$ is accepted, then

$$\left|T_{\mathrm{amb}} + \Delta\, y_{10} - T(\tau)\right| \le \frac{|\Delta|}{10}, \qquad T(t) = T_{\mathrm{amb}} + \Delta\, e^{-t/\tau}.$$
