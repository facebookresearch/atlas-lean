# Hudson–Kreitman–Aguadé statistic

For $L$ loci, sample sizes $n_A, n_B$, parameters $\theta_1, \dots, \theta_L, T, f$ and counts $S^A_i, S^B_i, D_i$ (polymorphism in species $A$ and $B$, divergence), the HKA statistic is

$$X^2 = \sum_{i=1}^{L} \Bigl(\frac{(S^A_i - m_S(\theta_i, n_A))^2}{v_S(\theta_i, n_A)} + \frac{(S^B_i - m_S(f\theta_i, n_B))^2}{v_S(f\theta_i, n_B)} + \frac{(D_i - m_D(\theta_i, T, f))^2}{v_D(\theta_i, T, f)}\Bigr),$$

with the [means](hka-poly-mean.md) $m_S, m_D$, the [variances](hka-poly-var.md) $v_S, v_D$ and the convention $x/0 = 0$.
