# Aipw ATEScore

Let $(\Omega, \mu)$ be a measure space and $X : \Omega \to \mathcal{X}$ a covariate. For a treatment event $T \subseteq \Omega$, a treatment propensity $e : \mathcal{X} \to \mathbb{R}$, arm regressions $m_0, m_1 : \mathcal{X} \to \mathbb{R}$ and an outcome $Y : \Omega \to \mathbb{R}$, the AIPW score for the average treatment effect is the missing-outcome AIPW score of the treated arm (response event $T$, propensity $e$, regression $m_1$) minus that of the control arm (response event $T^c$, propensity $1 - e$, regression $m_0$):

$$\psi(\omega) = m_1(X) + \mathbf{1}_T(\omega)\, \frac{Y(\omega) - m_1(X)}{e(X)} - m_0(X) - \mathbf{1}_{T^c}(\omega)\, \frac{Y(\omega) - m_0(X)}{1 - e(X)},$$

with $X = X(\omega)$ and the convention $a / 0 = 0$. It is applied to the observed outcome $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$.
