# Augmented IPWScore

Let $(\Omega, \mu)$ be a measure space, $X : \Omega \to \mathcal{X}$ a covariate with values in a measurable space, $T \subseteq \Omega$ the treatment event, $Y$ the observed outcome and $Y_0, Y_1$ the potential outcomes. For a propensity $e : \mathcal{X} \to \mathbb{R}$ and an augmentation function $h : \mathcal{X} \to \mathbb{R}$, the augmented IPW score is

$$\psi_h = \mathbf{1}_T \, \frac{Y}{e(X)} - \mathbf{1}_{T^c} \, \frac{Y}{1 - e(X)} - \bigl(\mathbf{1}_T - e(X)\bigr)\, h(X),$$

with the convention $x / 0 = 0$. With $h = 0$ it is the IPW contrast; where $e(X) \notin \{0, 1\}$, $h = m_1/e + m_0/(1 - e)$ gives the AIPW score.
