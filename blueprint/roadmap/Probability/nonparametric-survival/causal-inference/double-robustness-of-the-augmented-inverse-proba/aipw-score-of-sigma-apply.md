# Aipw Score Of Sigma apply

Let $T \subseteq \Omega$ and $Y, e, g_0, g_1 : \Omega \to \mathbb{R}$. The AIPW score, defined as the treated-arm score $g_1 + \mathbf{1}_T (Y - g_1)/e$ minus the control-arm score $g_0 + \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$, is for every $\omega \in \Omega$ the single contrast

$$\psi(e, g_0, g_1)(\omega) = g_1(\omega) - g_0(\omega) + \mathbf{1}_T(\omega) \, \frac{Y(\omega) - g_1(\omega)}{e(\omega)} - \mathbf{1}_{T^c}(\omega) \, \frac{Y(\omega) - g_0(\omega)}{1 - e(\omega)},$$

with the convention $x / 0 = 0$.
