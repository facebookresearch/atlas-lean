# Kl Div comp Prod gaussian Noise Kernel of scalar Power Bound

Let $m \in \mathbb{R}$, let $N > 0$ and $V > 0$, and let $\mu$ be a probability measure on $\mathbb{R}$ satisfying a power bound: for some $P \ge 0$,

$$\int x^2 \, d\mu(x) \le P,$$

the integral taken in $[0,\infty]$. Let $k$ be the additive Gaussian noise kernel $k_N(x) = \mathcal{N}(x, N)$, the law of $x + Z$ with $Z \sim \mathcal{N}(0, N)$. Then

$$\mathrm{KL}\big(\mu \otimes k \,\|\, \mu \times \mathcal{N}(m, V)\big) = \frac{1}{2}\left(\log\frac{V}{N} + \frac{N + \int (x - m)^2 \, d\mu(x)}{V} - 1\right),$$

with the right side read in $[0,\infty]$ (a real number $t$ is read as $\max(t,0)$).
