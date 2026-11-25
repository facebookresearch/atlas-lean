# Posterior stochastic ordering, cross-multiplied form

Let $\mu$ be a measure on $\mathbb{R}$ (the prior) and $L$ a likelihood family with a [monotone likelihood ratio](has-monotone-likelihood-ratio-on.md) on a set $S$ carrying the prior, $\mu(S^c) = 0$, such that every $L(n, \cdot)$ is $\mu$-integrable. Then for $n \le m$ and every threshold $t \in \mathbb{R}$,

$$\Big(\int_{\theta > t} L(n, \theta)\, d\mu\Big)\Big(\int L(m, \theta)\, d\mu\Big) \le \Big(\int_{\theta > t} L(m, \theta)\, d\mu\Big)\Big(\int L(n, \theta)\, d\mu\Big).$$

## Sources

- P. R. Milgrom, *Good news and bad news: representation theorems and applications*, Bell J. Econ. 12 (1981), 380–391, Proposition 1.
