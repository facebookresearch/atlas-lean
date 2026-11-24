# Moment duality, one generation

For all natural numbers $M \ne 0$ and $n$ and every $x \in [0, 1]$, if $X$ has the binomial distribution $\mathrm{Bin}(M, x)$, then

$$\mathbb{E}\Bigl[\Bigl(\frac{X}{M}\Bigr)^{n}\Bigr] = \sum_{k=0}^{n} p_M(n, k)\, x^k,$$

where $p_M(n, k)$ is the probability that $n$ genes have $k$ distinct parents in a Wright–Fisher population of $M$ gene copies ([Wright–Fisher transition probability of the lineage count](../../../coalescent-theory/ancestral-lineage-counting-and-tavar-s-formula/wf-lineage-prob.md)).
