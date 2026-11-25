# Aipw Fitted Score const

Let $O_i : \Omega \to \Omega_1$ ($i \in \mathbb N$) be random units, $T \subseteq \Omega_1$ a treatment event, $X : \Omega_1 \to \mathcal X$ a covariate and $Y : \Omega_1 \to \mathbb R$ an outcome, and let $e, m_0, m_1 : \mathcal X \to \mathbb R$ be fixed nuisance functions. If the fitted nuisances are constant in $n$, $i$ and $\omega$ and equal to $e, m_0, m_1$, then for every $n$, $i$ and $\omega$ the fitted AIPW score of unit $i$ at sample size $n$ is the AIPW score at its observation:

$$\hat\psi_{n,i}(\omega) = \psi_{e,m_0,m_1}\bigl(O_i(\omega)\bigr),$$

where

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

with $x/0 = 0$.
