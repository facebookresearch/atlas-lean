# Kullback–Leibler divergence between real Gaussians

Let $m_1, m_2 \in \mathbb{R}$ and let $v_1, v_2 \ge 0$ be variances with $v_1 > 0$ and $v_2 > 0$. The Kullback–Leibler divergence (in nats) of the Gaussian law $\mathcal N(m_1, v_1)$ from $\mathcal N(m_2, v_2)$ on $\mathbb{R}$ is

$$\mathrm{KL}\big(\mathcal N(m_1, v_1)\,\big\|\,\mathcal N(m_2, v_2)\big) = \frac{1}{2}\left(\log\frac{v_2}{v_1} + \frac{v_1 + (m_1 - m_2)^2}{v_2} - 1\right),$$

where the right side is viewed as an extended nonnegative real (a negative value would be read as $0$).
