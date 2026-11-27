# Real Rényi divergence

For probability mass functions $P, Q$ on a finite type and $\alpha \in \mathbb{R}$, the real Rényi divergence of order $\alpha$ is

$$
\frac{1}{\alpha - 1} \log \sum_{w} \frac{P(w)^{\alpha}}{Q(w)^{\alpha - 1}},
$$

the logarithm of the [real Rényi moment](renyi-moment-real.md) scaled by $1/(\alpha - 1)$, with the conventions $1/0 = 0$ and $\log 0 = 0$. For $\alpha \ne 1$, outcomes with $Q(w) = 0$ contribute $0$ to the sum ($0^{\alpha - 1} = 0$ and division by zero is read as $0$); under support inclusion these are exactly the outcomes with $P(w) = Q(w) = 0$, so for $\alpha > 1$ the sum runs over $\{w : Q(w) > 0\}$.
