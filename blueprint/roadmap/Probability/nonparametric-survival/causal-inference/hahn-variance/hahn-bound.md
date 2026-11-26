# Hahn's variance expression at a center

Let $(\Omega, \mu)$ be a measure space, $X : \Omega \to \mathcal{X}$ a covariate with values in a measurable space, $T \subseteq \Omega$ the treatment event, $Y$ the observed outcome and $Y_0, Y_1$ the potential outcomes. For functions $e, m_0, m_1, s_0, s_1 : \mathcal{X} \to \mathbb{R}$ (propensity, outcome regressions and conditional variances of $Y_0, Y_1$ given $X$) and a center $\tau \in \mathbb{R}$, Hahn's variance expression at $\tau$ is

$$B(\tau) = \int_\Omega \left(\frac{s_1(X)}{e(X)} + \frac{s_0(X)}{1 - e(X)} + \bigl(m_1(X) - m_0(X) - \tau\bigr)^2\right) d\mu,$$

with the convention $x / 0 = 0$ and the integral equal to $0$ when the integrand is not integrable.

The expression is defined for every real center. Only at the true center $\tau = \int (Y_1 - Y_0)\, d\mu$, under the hypotheses of [Hahn's setting](hahn-setup.md) (with $e$, $m_a$ and $s_a$ the actual propensity, outcome regressions and conditional variances), is it [the variance of the AIPW score](variance-aipw-score.md) and [the least variance of an augmented IPW score](hahn-bound-le-variance-augmented-ipwscor.md), Hahn's semiparametric variance bound. At another center it need not be a variance: with both potential outcomes $0$, propensity $1/2$ and center $1$ the expression is $1$, while the score is identically $0$.
