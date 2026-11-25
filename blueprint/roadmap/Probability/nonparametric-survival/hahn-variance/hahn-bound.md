# Hahn's variance bound

Let $(\Omega, \mu)$ be a measure space, $X : \Omega \to \mathcal{X}$ a covariate with values in a measurable space, $T \subseteq \Omega$ the treatment event, $Y$ the observed outcome and $Y_0, Y_1$ the potential outcomes. For functions $e, m_0, m_1, s_0, s_1 : \mathcal{X} \to \mathbb{R}$ (propensity, outcome regressions and conditional variances of $Y_0, Y_1$ given $X$) and a center $\tau \in \mathbb{R}$, Hahn's variance bound for the average treatment effect is

$$B(\tau) = \int_\Omega \left(\frac{s_1(X)}{e(X)} + \frac{s_0(X)}{1 - e(X)} + \bigl(m_1(X) - m_0(X) - \tau\bigr)^2\right) d\mu,$$

with the convention $x / 0 = 0$ and the integral equal to $0$ when the integrand is not integrable.
