# Consistency of the plug-in variance estimator

Let $(\Omega, P)$ be a probability space, $\mu_1$ a measure on a measurable space $\Omega_1$, and $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) mutually independent random units, each with law $\mu_1$. Let $T \subseteq \Omega_1$, $X : \Omega_1 \to \mathcal X$, $Y : \Omega_1 \to \mathbb R$, and let $\psi = \psi_{e,m_0,m_1}$ be the AIPW score at fixed nuisances $e, m_0, m_1 : \mathcal X \to \mathbb R$,

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

(with $x/0=0$). Assume $\psi$ is measurable and $\psi \in L^2(\mu_1)$. Let $e_n^i(\omega), m_{0,n}^i(\omega), m_{1,n}^i(\omega)$ be fitted nuisances (functions $\mathcal X \to \mathbb R$ depending on $n$, $i$ and $\omega$), write $\hat\psi_{n,i}(\omega)$ for the fitted scores $\psi_{e_n^i(\omega), m_{0,n}^i(\omega), m_{1,n}^i(\omega)}(O_i(\omega))$, and let $\hat\sigma_n^2 = n^{-1}\sum_{i<n}(\hat\psi_{n,i} - \hat\tau_n)^2$ be the plug-in variance estimator, where $\hat\tau_n = n^{-1}\sum_{i<n}\hat\psi_{n,i}$.

Suppose the fitted scores are consistent for $\psi$ in empirical $L^2$:

$$\frac1n \sum_{i<n} \bigl(\hat\psi_{n,i} - \psi(O_i)\bigr)^2 \to 0 \quad \text{in } P\text{-probability}.$$

Then $\hat\sigma_n^2 \to \operatorname{Var}_{\mu_1}[\psi]$ in $P$-probability; this is also $\operatorname{Var}(\varphi)$ for $\varphi = \psi - \tau$, $\tau = \int\psi\,d\mu_1$.
