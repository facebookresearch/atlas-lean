# Ten Euler steps of bath cooling are within $|\Delta|/10$

Let $C, G > 0$, let $T_{\mathrm{amb}}, \Delta \in \mathbb{R}$, write $Q(T) = -G\,(T - T_{\mathrm{amb}})$ for the power delivered by the bath and $\tau = C/G$ for the thermal time constant. Let $T(t) = T_{\mathrm{amb}} + \Delta\, e^{-t/\tau}$ be the exact cooling trajectory, and let $X : \mathbb{N} \to \mathbb{R}$ satisfy $X_0 = T_{\mathrm{amb}} + \Delta$ and

$$X_{j+1} = X_j + \frac{\tau}{10}\,\frac{Q(X_j)}{C} \quad \text{for all } j.$$

Then

$$\left| X_{10} - T(\tau) \right| \le \frac{|\Delta|}{10}.$$
