# The AIPW score as an augmented IPW contrast

Let $X : \Omega \to \mathcal{X}$ be a covariate, $T \subseteq \Omega$ the treatment event, $Y : \Omega \to \mathbb{R}$ the observed outcome, and $e, m_0, m_1 : \mathcal{X} \to \mathbb{R}$ a candidate propensity and candidate outcome regressions. Let $\psi = m_1(X) - m_0(X) + \mathbf{1}_T (Y - m_1(X))/e(X) - \mathbf{1}_{T^c} (Y - m_0(X))/(1 - e(X))$ be the AIPW score, with $a / 0 = 0$. Let $\omega \in \Omega$ with $e(X(\omega)) \ne 0$ and $e(X(\omega)) \ne 1$, and write $x = X(\omega)$. Then

$$\psi(\omega) = \mathbf{1}_T(\omega) \, \frac{Y(\omega)}{e(x)} - \mathbf{1}_{T^c}(\omega) \, \frac{Y(\omega)}{1 - e(x)} - \bigl(\mathbf{1}_T(\omega) - e(x)\bigr)\left(\frac{m_1(x)}{e(x)} + \frac{m_0(x)}{1 - e(x)}\right):$$

the IPW contrast minus the propensity residual times $m_1/e + m_0/(1 - e)$ at $x$.
