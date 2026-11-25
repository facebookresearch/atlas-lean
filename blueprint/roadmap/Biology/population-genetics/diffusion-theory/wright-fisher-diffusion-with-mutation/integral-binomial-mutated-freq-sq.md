# Infinitesimal variance of the Wright–Fisher chain with mutation

Let $M \ge 1$ be a natural number, $\theta_1$ and $\theta_2$ real numbers, and $u_1, u_2 \in [0, 1]$ with $u_1 = \theta_1/(2M)$ and $u_2 = \theta_2/(2M)$. For $x \in [0, 1]$, let $p' = x + \frac{\theta_1(1 - x) - \theta_2 x}{2M}$ be the [frequency after mutation](mutated-freq.md) and let $k$ have the binomial distribution $\mathrm{Bin}(M, p')$. Then

$$M\, \mathbb{E}\Bigl[\Bigl(\frac{k}{M} - x\Bigr)^2\Bigr] = p'(1 - p') + \frac{\bigl(\theta_1(1 - x) - \theta_2 x\bigr)^2}{4M}.$$

As $M \to \infty$ with $\theta_1$, $\theta_2$ and $x$ fixed, the right side tends to $x(1 - x)$, the diffusion coefficient of the [mutation generator](mutation-generator.md).
