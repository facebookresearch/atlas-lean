# Query false-positive bound for sequence Bloom trees

**Setting.** A node of a sequence Bloom tree reports a query string $q$ when at least a fraction $\theta \in (0,1)$ of the distinct $k$-mers of $q$ test positive in the node's Bloom filter $U$. Let $q$ contain $\ell$ distinct $k$-mers, none of which is truly in $U$, and let $\xi$ be the false-positive rate of $U$ (for example $\xi = (1/2)^{h^*}$ as in [Union Bloom filter size and optimal hash count](union-bloom-filter-size-and-optimal-hash-count.md)).

**Theorem 2.** If the $\ell$ $k$-mers of $q$ are treated as independent filter queries, the probability that more than $\lfloor\theta\ell\rfloor$ of them are false positives in $U$ is

$$1 - \sum_{i=0}^{\lfloor\theta\ell\rfloor}\binom{\ell}{i}\xi^i(1-\xi)^{\ell-i}.$$

If moreover $\theta \ge \xi$, this probability is at most

$$\exp\!\left(-\frac{\ell(\theta-\xi)^2}{2(1-\xi)}\right),$$

so it is nearly $0$ when $\xi \ll \theta$ and $\ell$ is large.

## Depends on

- [Union Bloom filter size and optimal hash count](union-bloom-filter-size-and-optimal-hash-count.md)

## Expansion

The number $X$ of false-positive $k$-mers is $\mathrm{Binomial}(\ell,\xi)$, which gives the exact expression. With $Y = \ell - X$ the number of correctly rejected $k$-mers, $\Pr[X > \theta\ell] = \Pr[Y < \ell - \theta\ell]$, and when $\theta \ge \xi$ the threshold $\ell - \theta\ell$ lies below $\mathbb{E}[Y] = \ell(1-\xi)$; the lower-tail Chernoff bound gives the exponential estimate. With the natural search threshold $\theta = 1/2$, a filter rate of a few percent makes false descents through the tree exponentially unlikely in the query length, which is why the tree tolerates much higher per-$k$-mer false-positive rates than a single-$k$-mer index would.

## Sources

- B. Solomon, C. Kingsford, "Fast search of thousands of short-read sequencing experiments", Nature Biotechnology 34(3) (2016) 300–302, Online Methods, Theorem 2, Eqs. (4)–(5), <https://doi.org/10.1038/nbt.3442>, PMCID PMC4804353.
