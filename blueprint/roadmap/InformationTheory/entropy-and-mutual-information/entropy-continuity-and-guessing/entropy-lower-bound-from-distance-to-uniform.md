# Shannon entropy lower bound from statistical distance to uniform

Let $p$ be a distribution on $\{0,1\}^n$, $U_n$ the uniform distribution and $\delta = \delta(p, U_n)$ their statistical distance. Then the Shannon entropy in bits satisfies

$$
H(p) \ge (n - 1)(1 - 2\delta).
$$

In particular, if $n \ge 1$ and $\delta \le 1/n^2$ then $H(p) \ge n - 2$. Moreover, truncating a distribution on $\{0,1\}^m$ to its first $k \le m$ bits lowers its entropy by at most $m - k$, and appending $k$ independent uniform bits raises it by exactly $k$.

## Proof sketch

The mass of outcomes with $p(x) > 2^{-(n-1)}$ is at most $2\delta$, because on that set $p$ exceeds the uniform mass by at least half of $p$. Every other outcome contributes surprisal at least $n - 1$, so $H(p) \ge (n-1)(1 - 2\delta)$. With $\delta \le 1/n^2$, $(n-1)(1 - 2/n^2) \ge n - 2$ for $n \ge 1$.

## Depends on

- [Shannon entropy](../shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", IEEE 61st Annual Symposium on Foundations of Computer Science (FOCS), 2020.
