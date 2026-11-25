# Continuous binom Tail

For $n, k \in \mathbb{N}$ and $p \in \mathbb{R}$, write

$$B(n, k, p) = \sum_{i = k}^{n} \binom{n}{i} p^i (1 - p)^{n - i}$$

for the upper tail $P(X \ge k)$ of $X \sim \mathrm{Bin}(n, p)$ (defined by this polynomial for every real $p$, with $0^0 = 1$). For all $n, k \in \mathbb{N}$, the map $p \mapsto B(n, k, p)$ is continuous on $\mathbb{R}$.
