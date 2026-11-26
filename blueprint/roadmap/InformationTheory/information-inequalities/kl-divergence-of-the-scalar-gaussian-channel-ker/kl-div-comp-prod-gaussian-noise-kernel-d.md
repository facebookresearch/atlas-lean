# Kl Div comp Prod gaussian Noise Kernel dirac

Let $m, a \in \mathbb{R}$ and let $N > 0$, $V > 0$. Let $k$ be the additive Gaussian noise kernel $k_N(x) = \mathcal{N}(x, N)$, the law of $x + Z$ with $Z \sim \mathcal{N}(0, N)$. For the point-mass input $\delta_a$,

$$\mathrm{KL}\big(\delta_a \otimes k \,\|\, \delta_a \times \mathcal{N}(m, V)\big) = \frac{1}{2}\left(\log\frac{V}{N} + \frac{N + (a - m)^2}{V} - 1\right),$$

with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
