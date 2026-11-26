# Measurable aipw Score

Let $\Omega_1$ and $\mathcal X$ be measurable spaces, $T \subseteq \Omega_1$ a measurable set, $X : \Omega_1 \to \mathcal X$ and $Y : \Omega_1 \to \mathbb R$ measurable, and $e, m_0, m_1 : \mathcal X \to \mathbb R$ measurable. Then the AIPW score

$$\psi_{e,m_0,m_1}(o) = m_1(X(o)) - m_0(X(o)) + \mathbf 1_T(o)\,\frac{Y(o) - m_1(X(o))}{e(X(o))} - \mathbf 1_{T^c}(o)\,\frac{Y(o) - m_0(X(o))}{1 - e(X(o))},$$

(with $x/0 = 0$) is a measurable function of $o \in \Omega_1$.
