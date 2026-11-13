# Extending a signed power-of-two sum to a longer range

Let $m \ge 1$, $s$, $t$ and $\alpha$
be natural numbers, let $\beta = \nu_2(m + 1)$ be the exponent of $2$ in $m + 1$, and suppose that
$s + \beta \le t + 1$ and $2^\alpha \equiv 1 \pmod{(m + 1)/2^\beta}$. If an integer $n$ can be
written as $\sum_{j=s}^{t} \lambda_j 2^j$ with every $\lambda_j \in \{-1, m\}$, then $n$ can also be
written as $\sum_{j=s}^{t+\alpha} \mu_j 2^j$ with every $\mu_j \in \{-1, m\}$.

The source's hypothesis $t \ge s + \beta - 1$ is written as $s + \beta \le t + 1$ to cover the
case $\beta = 0$.

## Sources

- Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Corollary 8 (`jis-2024-24.7.5-cor-8`): fix `m ≥ 1` and let `β = ν₂(m + 1)`. If `n` is a signed power-of-two sum over `[s, t]` with `t ≥ s + β - 1`, then `n` is also expressible over `[s, t + α]` whenever `2^α ≡ 1 [(m + 1) / 2^β]`.
