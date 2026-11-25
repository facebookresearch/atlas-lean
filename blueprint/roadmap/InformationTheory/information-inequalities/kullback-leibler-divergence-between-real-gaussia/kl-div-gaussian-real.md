# Scalar Gaussian divergence

Let $m_1, m_2 \in \mathbb{R}$ and let $v_1, v_2 > 0$ be variances (not standard deviations). The Kullback-Leibler divergence, in nats, between the real Gaussians $\mathcal{N}(m_1, v_1)$ and $\mathcal{N}(m_2, v_2)$ is finite and equals

$$\mathrm{KL}\big(\mathcal{N}(m_1, v_1) \,\|\, \mathcal{N}(m_2, v_2)\big) = \frac{1}{2}\left(\log\frac{v_2}{v_1} + \frac{v_1 + (m_1 - m_2)^2}{v_2} - 1\right),$$

with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
