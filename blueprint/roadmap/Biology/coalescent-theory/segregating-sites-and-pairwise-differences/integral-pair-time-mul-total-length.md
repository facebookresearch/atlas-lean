# Pair coalescence time against the total branch length

Let $\mu$ be a probability measure, let $(T_k)$ be Kingman holding times of a sample of size $n \ge 2$ under $\mu$, with total branch length $L$, and let $\chi_k$ ($k \in \mathbb{N}$) be real random variables. Suppose that $\tau = \sum_{k=2}^{n} \chi_k T_k$ and that

$$\mathbb{E}[\chi_k T_k T_{k'}] = p_{n,k}\, \mathbb{E}[T_k T_{k'}] \quad \text{for all } k, k' \in \{2, \dots, n\},$$

where $p_{n,k}$ is the [probability that a pair lies in separate lineages](pair-separate-prob.md). Then

$$\mathbb{E}[\tau L] = 2\, a_1(n) + \frac{n+2}{n},$$

with [Tajima's constant](tajima-a1.md) $a_1(n)$. In the coalescent, $\tau$ is the coalescence time of a pair and $\chi_k$ indicates that the pair is still in two distinct lineages while there are $k$ lineages; only the factorization is used, so $\chi_k$ need not be an indicator.
