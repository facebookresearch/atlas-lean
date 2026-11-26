# Epsilon-complementary slackness implies near-optimality

If $\sigma$ and $p$ satisfy $\varepsilon$-complementary slackness, then

$$
\sum_i c(i, \sigma(i)) \le \sum_i c(i, \tau(i)) + n\varepsilon
$$

for every permutation $\tau$. In particular, if all costs are multiples of $n + 1$ and $\varepsilon = 1$, then $\sigma$ is optimal.

## Proof sketch

Summing the slackness inequalities and using that both $\sigma$ and $\tau$ are bijections, the prices cancel: $\sum_i c(i, \sigma(i)) - n\varepsilon \le \sum_i u_i + \sum_j p_j - \sum_j p_j \le \sum_i c(i, \tau(i))$. With scaled costs the gap $n < n+1$ is below the smallest positive cost difference.

## Depends on

- [Epsilon-complementary slackness for the assignment problem](epsilon-complementary-slackness.md)

## Sources

- D. P. Bertsekas, "Network Optimization: Continuous and Discrete Models", Athena Scientific, 1998.
