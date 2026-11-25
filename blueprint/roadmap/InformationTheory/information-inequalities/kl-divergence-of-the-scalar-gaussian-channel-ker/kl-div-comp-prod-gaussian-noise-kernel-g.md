# Kl Div comp Prod gaussian Noise Kernel gaussian Real

Let $m, \mu_0 \in \mathbb{R}$, let $N > 0$, $V > 0$ and $s \ge 0$. Let $k$ be the additive Gaussian noise kernel $k_N(x) = \mathcal{N}(x, N)$, the law of $x + Z$ with $Z \sim \mathcal{N}(0, N)$. For the Gaussian input $\mathcal{N}(\mu_0, s)$,

$$\mathrm{KL}\big(\mathcal{N}(\mu_0, s) \otimes k \,\|\, \mathcal{N}(\mu_0, s) \times \mathcal{N}(m, V)\big) = \frac{1}{2}\left(\log\frac{V}{N} + \frac{N + s + (\mu_0 - m)^2}{V} - 1\right),$$

with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
