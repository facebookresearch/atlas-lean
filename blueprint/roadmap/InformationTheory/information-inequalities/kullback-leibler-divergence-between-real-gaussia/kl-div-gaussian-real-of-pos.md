# Kl Div gaussian Real of pos

Let $m_1, m_2, s, t \in \mathbb{R}$ with $s > 0$ and $t > 0$, and regard $s$ and $t$ as variances. Then

$$\mathrm{KL}\big(\mathcal{N}(m_1, s) \,\|\, \mathcal{N}(m_2, t)\big) = \frac{1}{2}\left(\log\frac{t}{s} + \frac{s + (m_1 - m_2)^2}{t} - 1\right),$$

the Kullback-Leibler divergence in nats, with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
