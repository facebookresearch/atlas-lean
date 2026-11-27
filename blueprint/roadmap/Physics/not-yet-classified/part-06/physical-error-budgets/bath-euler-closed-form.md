# Euler recurrence for bath cooling at step $\tau/10$

Let $C, G > 0$, let $T_{\mathrm{amb}}, \Delta \in \mathbb{R}$, write $Q(T) = -G\,(T - T_{\mathrm{amb}})$ for the power delivered by the bath and $\tau = C/G$ for the thermal time constant. Let $X : \mathbb{N} \to \mathbb{R}$ satisfy $X_0 = T_{\mathrm{amb}} + \Delta$ and the explicit Euler recurrence

$$X_{j+1} = X_j + \frac{\tau}{10}\,\frac{Q(X_j)}{C} \quad \text{for all } j.$$

Then for every $j \in \mathbb{N}$,

$$X_j = T_{\mathrm{amb}} + \Delta \left(\tfrac{9}{10}\right)^j.$$
