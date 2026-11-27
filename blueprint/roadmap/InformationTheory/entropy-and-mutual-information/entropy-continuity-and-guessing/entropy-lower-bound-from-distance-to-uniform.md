# Shannon entropy lower bound from statistical distance to uniform

Let $n \ge 4$, let $p$ be a distribution on $\{0,1\}^n$, $U_n$ the uniform distribution and $\delta = \delta(p, U_n)$ their statistical distance. If $\delta \le 1/n^2$, then the Shannon entropy in bits satisfies

$$
H(p) \ge n - 2.
$$

## Proof sketch

Let $S$ be the set of outcomes with $p(x) \le 2^{-(n-1)}$. Every outcome outside $S$ has $p(x) \ge 2 \cdot 2^{-n}$, so it contributes at least $p(x)/2$ to $\sum_x |p(x) - 2^{-n}|$, which is $2\delta$; hence $p(S^c) \le 4\delta \le 4/n^2$. Every outcome in $S$ has surprisal at least $n - 1$, so $H(p) \ge (1 - 4/n^2)(n - 1) \ge n - 4/n - 1 \ge n - 2$ for $n \ge 4$.

A sharper form holds for every $n$: $H(p) \ge (n - 1)(1 - 2\delta)$. The mass of outcomes with $p(x) > 2^{-(n-1)}$ is at most $2\delta$, because on that set $p$ exceeds the uniform mass by at least half of $p$. Every other outcome contributes surprisal at least $n - 1$, so $H(p) \ge (n-1)(1 - 2\delta)$. With $\delta \le 1/n^2$, $(n-1)(1 - 2/n^2) \ge n - 2$ for $n \ge 1$, so the conclusion extends to every $n \ge 1$.

Two related facts follow from the chain rule $H(X, Y) = H(X) + H(Y \mid X)$: truncating a distribution on $\{0,1\}^m$ to its first $k \le m$ bits lowers its entropy by at most $m - k$, since the dropped bits have conditional entropy at most $m - k$; and appending $k$ independent uniform bits raises it by exactly $k$.

## Depends on

- [Shannon entropy](../shannon-entropy-and-kullback-leibler-divergence/shannon-entropy.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- Y. Liu and R. Pass, "On One-way Functions and Kolmogorov Complexity", IEEE 61st Annual Symposium on Foundations of Computer Science (FOCS), 2020, Section 2.5, Lemma 2.2.
