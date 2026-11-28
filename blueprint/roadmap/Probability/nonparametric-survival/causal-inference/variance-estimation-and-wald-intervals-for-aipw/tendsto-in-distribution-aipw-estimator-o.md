# Oracle central limit theorem for the AIPW estimator

Let $(\Omega, P)$ and $(\Omega', P')$ be probability spaces, $\mu_1$ a measure on a measurable space $\Omega_1$, and $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) mutually independent random units, each with law $\mu_1$. Let $T \subseteq \Omega_1$, $X : \Omega_1 \to \mathcal X$, $Y : \Omega_1 \to \mathbb R$, and let $\psi = \psi_{e,m_0,m_1}$ be the AIPW score at fixed nuisances $e, m_0, m_1 : \mathcal X \to \mathbb R$,

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

(with $x/0=0$). Assume $\psi$ is measurable and $\psi \in L^2(\mu_1)$. Let $\tau = \int \psi \, d\mu_1$ and let $Z : \Omega' \to \mathbb R$ have law $N(0, \operatorname{Var}_{\mu_1}[\psi])$ under $P'$.

Let $\hat\tau_n^* = n^{-1}\sum_{i<n} \psi(O_i)$ be the AIPW estimator with these fixed nuisances. Then

$$\sqrt n\,(\hat\tau_n^* - \tau) \xrightarrow{d} Z \quad (n \to \infty).$$
