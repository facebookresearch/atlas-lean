# Conditional error bound for the count of significant axes

Let $P$ be a measure on a measurable space $\Omega$, let $T : \Omega \to (\mathbb{N} \to \mathbb{R})$ assign to each outcome a sequence of statistics, let $F : \mathbb{R} \to \mathbb{R}$, $t \in \mathbb{R}$ and $K, k \in \mathbb{N}$, and suppose that

$$P(\{\omega : T_k(\omega) > t\}) \le \max(1 - F(t), 0).$$

Then the [sequential count](num-significant.md) satisfies

$$P(\{\omega : n_t(K)(\omega) > k\}) \le \max(1 - F(t), 0).$$

With $F$ the Tracy–Widom distribution function and $P$ the null distribution, the hypothesis is the Tracy–Widom approximation for the $k$-th statistic, assumed here rather than derived.
