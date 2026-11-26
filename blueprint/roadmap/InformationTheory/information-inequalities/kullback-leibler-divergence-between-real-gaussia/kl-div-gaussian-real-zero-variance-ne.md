# The closed form fails for a zero first variance

Let $m_1, m_2 \in \mathbb{R}$ and let $v_2 > 0$ be a variance. At zero first variance the divergence is not given by the closed form:

$$\mathrm{KL}\big(\mathcal{N}(m_1, 0) \,\|\, \mathcal{N}(m_2, v_2)\big) \neq D(m_1, m_2, 0, v_2),$$

where $D(m_1, m_2, v_1, v_2) = \frac{1}{2}\left(\log\frac{v_2}{v_1} + \frac{v_1 + (m_1 - m_2)^2}{v_2} - 1\right)$ with the conventions $x / 0 = 0$ and $\log 0 = 0$, is converted to a value in $[0, \infty]$ by $\max(D, 0)$, which sends a negative value to $0$ and is always finite. The left side is $\infty$, so the positivity hypothesis on $v_1$ in the closed-form formula cannot be dropped.
