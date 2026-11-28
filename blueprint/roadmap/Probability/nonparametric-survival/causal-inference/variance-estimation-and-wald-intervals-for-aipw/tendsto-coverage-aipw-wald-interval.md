# Asymptotic coverage of the AIPW Wald interval

Let $(\Omega, P)$ be a probability space, $\mu_1$ a measure on a measurable space $\Omega_1$, and $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) mutually independent random units, each with law $\mu_1$. Let $T \subseteq \Omega_1$, $X : \Omega_1 \to \mathcal X$, $Y : \Omega_1 \to \mathbb R$, and let $\psi = \psi_{e,m_0,m_1}$ be the AIPW score at fixed nuisances $e, m_0, m_1 : \mathcal X \to \mathbb R$,

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

(with $x/0=0$). Assume $\psi$ is measurable and $\psi \in L^2(\mu_1)$. Let $e_n^i(\omega), m_{0,n}^i(\omega), m_{1,n}^i(\omega)$ be fitted nuisances (functions $\mathcal X \to \mathbb R$ depending on $n$, $i$ and $\omega$), and write $\hat\psi_{n,i}(\omega) = \psi_{e_n^i(\omega), m_{0,n}^i(\omega), m_{1,n}^i(\omega)}(O_i(\omega))$ for the fitted scores. Assume each $\hat\psi_{n,i}$ is $P$-a.e. measurable. Let $\hat\tau_n = n^{-1}\sum_{i<n}\hat\psi_{n,i}$ be the AIPW estimator and $\hat\tau_n^* = n^{-1}\sum_{i<n}\psi(O_i)$ the oracle estimator with the fixed nuisances. Let $\hat\sigma_n^2 = n^{-1}\sum_{i<n}(\hat\psi_{n,i} - \hat\tau_n)^2$ be the plug-in variance estimator, $\tau = \int\psi\,d\mu_1$, and assume $\operatorname{Var}_{\mu_1}[\psi] \ne 0$. Suppose

- $\sqrt n\,(\hat\tau_n - \hat\tau_n^*) \to 0$ in $P$-probability, and
- $n^{-1}\sum_{i<n}(\hat\psi_{n,i} - \psi(O_i))^2 \to 0$ in $P$-probability.

Then for every $z \in \mathbb R$, the probability that the Wald interval

$$\Bigl[\hat\tau_n - z\,\frac{\sqrt{\hat\sigma_n^2}}{\sqrt n},\ \hat\tau_n + z\,\frac{\sqrt{\hat\sigma_n^2}}{\sqrt n}\Bigr]$$

contains $\tau$ converges to $N(0,1)([-z, z])$ as $n \to \infty$. For $0 < \alpha < 1$ and $z$ the $1 - \alpha/2$ standard-normal quantile, this limit is $1 - \alpha$.
