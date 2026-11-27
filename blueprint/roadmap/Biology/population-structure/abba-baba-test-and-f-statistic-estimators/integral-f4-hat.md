# Unbiased f4 estimator under binomial sampling

Let $\mu$ be a measure, let $m_A, m_B, m_C, m_D \ge 1$ and $q_A, q_B, q_C, q_D \in [0, 1]$, and let $X_A, X_B, X_C, X_D$ have binomial laws $\mathrm{Bin}(m_A, q_A), \dots, \mathrm{Bin}(m_D, q_D)$ under $\mu$, with $X_A$ and $X_B$ each independent of $X_C$ and of $X_D$. Then the [f4 estimator](f4-hat.md) satisfies

$$\int \hat f_4(m_A, m_B, m_C, m_D, X_A, X_B, X_C, X_D) \, d\mu = (q_A - q_B)(q_C - q_D).$$
