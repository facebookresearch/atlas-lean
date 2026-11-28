# Aipw Fitted Score

Let $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) be random units, $T \subseteq \Omega_1$ a treatment event, $X : \Omega_1 \to \mathcal X$ a covariate and $Y : \Omega_1 \to \mathbb R$ an outcome, and let $e_n^i(\omega), m_{0,n}^i(\omega), m_{1,n}^i(\omega) : \mathcal X \to \mathbb R$ be nuisance functions that may depend on the sample size $n$, the unit $i$ and the sample point $\omega$.

The fitted AIPW score of unit $i$ at sample size $n$ is the AIPW score evaluated at that unit's observation with its fitted nuisances:

$$\hat\psi_{n,i}(\omega) = \psi_{e_n^i(\omega),\, m_{0,n}^i(\omega),\, m_{1,n}^i(\omega)}\bigl(O_i(\omega)\bigr),$$

where for $e, m_0, m_1 : \mathcal X \to \mathbb R$ the AIPW score is

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

with the convention $x / 0 = 0$.
