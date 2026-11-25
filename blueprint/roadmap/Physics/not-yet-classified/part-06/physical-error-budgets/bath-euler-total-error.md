# Three-term error budget for ten computed Euler steps

Let $C, G > 0$, let $T_{\mathrm{amb}}, \Delta \in \mathbb{R}$, write $Q(T) = -G\,(T - T_{\mathrm{amb}})$ for the power delivered by the bath and $\tau = C/G$ for the thermal time constant. Let $T(t) = T_{\mathrm{amb}} + \Delta\, e^{-t/\tau}$. Suppose some sequence $X : \mathbb{N} \to \mathbb{R}$ satisfies $X_0 = T_{\mathrm{amb}} + \Delta$ and $X_{j+1} = X_j + \frac{\tau}{10}\frac{Q(X_j)}{C}$ for all $j$. For any sequence $Y : \mathbb{N} \to \mathbb{R}$, with residuals

$$\eta_j = Y_{j+1} - \left(Y_j + \frac{\tau}{10}\,\frac{Q(Y_j)}{C}\right),$$

$$\left| Y_{10} - T(\tau) \right| \le \left(\tfrac{9}{10}\right)^{10} \left| Y_0 - (T_{\mathrm{amb}} + \Delta) \right| + \sum_{j=0}^{9} \left(\tfrac{9}{10}\right)^{9-j} |\eta_j| + \frac{|\Delta|}{10}.$$
