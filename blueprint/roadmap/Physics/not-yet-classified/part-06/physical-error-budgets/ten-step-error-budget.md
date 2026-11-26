# Ten-step Euler error budget

For $C, G, T_{\mathrm{amb}}, \Delta \in \mathbb{R}$ and a sequence $Y : \mathbb{N} \to \mathbb{R}$, let $\tau = C/G$, $Q(T) = -G\,(T - T_{\mathrm{amb}})$, and

$$\eta_j = Y_{j+1} - \left(Y_j + \frac{\tau}{10}\,\frac{Q(Y_j)}{C}\right).$$

The ten-step error budget is

$$B = \left(\tfrac{9}{10}\right)^{10} \left| Y_0 - (T_{\mathrm{amb}} + \Delta) \right| + \sum_{j=0}^{9} \left(\tfrac{9}{10}\right)^{9-j} |\eta_j| + \frac{|\Delta|}{10}.$$

For $C = 0$ or $G = 0$ the step term takes the convention $x/0 = 0$, so $\eta_j = Y_{j+1} - Y_j$.
