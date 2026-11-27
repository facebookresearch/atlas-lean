# The posterior is stochastically nondecreasing in the observation

Let $\mu$ be a measure on $\mathbb{R}$ and $L$ a likelihood family with a [monotone likelihood ratio](has-monotone-likelihood-ratio-on.md) on a set $S$ with $\mu(S^c) = 0$, every $L(n, \cdot)$ being $\mu$-integrable. If $n \le m$ and both marginal likelihoods $\int L(n, \cdot)\, d\mu$ and $\int L(m, \cdot)\, d\mu$ are positive, then for every $t \in \mathbb{R}$

$$\Pi(\theta > t \mid n) \le \Pi(\theta > t \mid m),$$

where $\Pi$ is the [posterior tail probability](posterior-tail.md).

## Sources

- P. R. Milgrom, *Good news and bad news: representation theorems and applications*, Bell J. Econ. 12 (1981), 380–391, Proposition 2.
