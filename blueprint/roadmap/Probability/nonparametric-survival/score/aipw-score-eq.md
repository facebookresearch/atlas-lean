# Aipw Score eq

Let $X : \Omega \to \mathcal{X}$ be a covariate, $T \subseteq \Omega$ the treatment event, $Y : \Omega \to \mathbb{R}$ the observed outcome, and $e, m_0, m_1 : \mathcal{X} \to \mathbb{R}$ a candidate propensity and candidate outcome regressions. Let $\psi = m_1(X) - m_0(X) + \mathbf{1}_T (Y - m_1(X))/e(X) - \mathbf{1}_{T^c} (Y - m_0(X))/(1 - e(X))$ be the AIPW score, with $a / 0 = 0$. Then for every $\omega \in \Omega$, writing $x = X(\omega)$,

$$\psi(\omega) = m_1(x) - m_0(x) + \mathbf{1}_T(\omega) \, \frac{Y(\omega) - m_1(x)}{e(x)} - \mathbf{1}_{T^c}(\omega) \, \frac{Y(\omega) - m_0(x)}{1 - e(x)},$$

where $\psi$ is defined as the treated-arm score $m_1(X) + \mathbf{1}_T (Y - m_1(X))/e(X)$ minus the control-arm score $m_0(X) + \mathbf{1}_{T^c} (Y - m_0(X))/(1 - e(X))$.
