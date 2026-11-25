# Consistency of the variance estimator, fixed nuisances

Let $(\Omega, P)$ be a probability space, $\mu_1$ a measure on a measurable space $\Omega_1$, and $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) mutually independent random units, each with law $\mu_1$. Let $T \subseteq \Omega_1$, $X : \Omega_1 \to \mathcal X$, $Y : \Omega_1 \to \mathbb R$, and let $\psi = \psi_{e,m_0,m_1}$ be the AIPW score at fixed nuisances $e, m_0, m_1 : \mathcal X \to \mathbb R$,

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

(with $x/0=0$). Assume $\psi$ is measurable and $\psi \in L^2(\mu_1)$.

Let $\hat\sigma_n^2 = n^{-1}\sum_{i<n}\bigl(\psi(O_i) - \hat\tau_n^*\bigr)^2$, with $\hat\tau_n^* = n^{-1}\sum_{i<n}\psi(O_i)$, be the plug-in variance estimator with the fixed nuisances. Then $\hat\sigma_n^2 \to \operatorname{Var}_{\mu_1}[\psi]$ in $P$-probability.
