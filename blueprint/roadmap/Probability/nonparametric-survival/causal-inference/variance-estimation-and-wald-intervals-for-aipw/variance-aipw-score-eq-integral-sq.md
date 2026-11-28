# Variance of the AIPW score as a centered second moment

Let $\mu_1$ be a measure on a measurable space $\Omega_1$, $T \subseteq \Omega_1$, $X : \Omega_1 \to \mathcal X$, $Y : \Omega_1 \to \mathbb R$ and $e, m_0, m_1 : \mathcal X \to \mathbb R$, and let $\psi$ be the AIPW score

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

(with $x/0 = 0$). Suppose $\psi$ is $\mu_1$-a.e. measurable and $\int \psi \, d\mu_1 = \tau$. Then the variance of $\psi$ is the second moment of the centered score $\varphi = \psi - \tau$:

$$\operatorname{Var}_{\mu_1}[\psi] = \int (\psi - \tau)^2 \, d\mu_1.$$

Here the real variance is the real part of the extended variance, so it is $0$ when the extended variance is infinite, and the integral is $0$ when its integrand is not integrable; when $\psi$ is not square-integrable both sides can therefore be $0$. For a square-integrable score on a probability space this is the usual identity between the variance and the second moment about the mean.
