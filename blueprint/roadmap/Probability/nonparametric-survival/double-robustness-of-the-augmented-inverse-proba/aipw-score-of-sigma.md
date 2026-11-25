# Aipw Score Of Sigma

Let $T \subseteq \Omega$ be the treatment event, $Y : \Omega \to \mathbb{R}$ the observed outcome, $e : \Omega \to \mathbb{R}$ a candidate propensity and $g_0, g_1 : \Omega \to \mathbb{R}$ candidate outcome regressions. The augmented inverse probability weighted (AIPW) score is

$$\psi(e, g_0, g_1) = g_1 - g_0 + \mathbf{1}_T \, \frac{Y - g_1}{e} - \mathbf{1}_{T^c} \, \frac{Y - g_0}{1 - e},$$

with the convention $x / 0 = 0$. It is the treated-arm missing-outcome AIPW score $g_1 + \mathbf{1}_T (Y - g_1)/e$ minus the control-arm score $g_0 + \mathbf{1}_{T^c} (Y - g_0)/(1 - e)$, with the identity map as covariate.
