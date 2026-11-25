# Aipw Score eq of consistency

Let $X : \Omega \to \mathcal{X}$ be a covariate, $T \subseteq \Omega$ the treatment event, $Y : \Omega \to \mathbb{R}$ the observed outcome, and $e, m_0, m_1 : \mathcal{X} \to \mathbb{R}$ a candidate propensity and candidate outcome regressions. Let $\psi = m_1(X) - m_0(X) + \mathbf{1}_T (Y - m_1(X))/e(X) - \mathbf{1}_{T^c} (Y - m_0(X))/(1 - e(X))$ be the AIPW score, with $a / 0 = 0$. Suppose consistency holds at every point: $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ for potential outcomes $Y_0, Y_1 : \Omega \to \mathbb{R}$. Then for every $\omega$, writing $x = X(\omega)$,

$$\psi(\omega) = m_1(x) - m_0(x) + \mathbf{1}_T(\omega) \, \frac{Y_1(\omega) - m_1(x)}{e(x)} - \mathbf{1}_{T^c}(\omega) \, \frac{Y_0(\omega) - m_0(x)}{1 - e(x)}.$$
