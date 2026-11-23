# Drift of the Wright–Fisher chain with mutation

Let $M \ge 1$ be a natural number, $\theta_1$ and $\theta_2$ real numbers, and $u_1, u_2 \in [0, 1]$ mutation probabilities with $u_1 = \theta_1/(2M)$ and $u_2 = \theta_2/(2M)$ (so $0 \le \theta_i \le 2M$). For $x \in [0, 1]$, let $p'$ be the [frequency after mutation](mutated-freq.md) and let $k$ have the binomial distribution $\mathrm{Bin}(M, p')$: one generation of the Wright–Fisher chain with mutation on $M = 2N$ gene copies. Then

$$M\Bigl(\mathbb{E}\Bigl[\frac{k}{M}\Bigr] - x\Bigr) = \frac{\theta_1(1 - x) - \theta_2 x}{2},$$

the drift coefficient of the [mutation generator](mutation-generator.md), for every such $M$.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004).
