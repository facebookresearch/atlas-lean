# Aipw Score

Let $X : \Omega \to \mathcal{X}$ be a covariate, $T \subseteq \Omega$ the treatment event, $Y : \Omega \to \mathbb{R}$ the observed outcome, and $e, m_0, m_1 : \mathcal{X} \to \mathbb{R}$ a candidate propensity and candidate outcome regressions, fixed functions of the covariate value. The AIPW score for the average treatment effect is

$$\psi = m_1(X) - m_0(X) + \mathbf{1}_T \, \frac{Y - m_1(X)}{e(X)} - \mathbf{1}_{T^c} \, \frac{Y - m_0(X)}{1 - e(X)}.$$

With the convention $a / 0 = 0$, a unit with $e(X) = 0$ (resp. $e(X) = 1$) has its treated (resp. control) residual dropped; positivity of the candidate rules this out. It is the treated-arm missing-outcome AIPW score minus the control-arm one.
