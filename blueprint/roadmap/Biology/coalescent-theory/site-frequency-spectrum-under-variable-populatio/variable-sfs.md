# Expected site frequency spectrum under variable population size

For a real number $\theta$, natural numbers $n$ and $i$, and real numbers $t_k$ ($k \in \mathbb{N}$), let

$$\xi_{n,i}(\theta, t) = \frac{\theta}{2} \sum_{k=2}^{n} g_{n,i,k}\, t_k,$$

with the [Griffiths–Tavaré kernel](sfs-kernel.md) $g_{n,i,k}$. The formula is defined for all indices and all reals. When $1 \le i < n$, $\theta \ge 0$ and $t_k$ is the mean holding time with $k$ lineages, it is the expected number of sites whose derived allele is carried by $i$ of the $n$ sample copies.

## Sources

- R. C. Griffiths and S. Tavaré, *The age of a mutation in a general coalescent tree*, Comm. Statist. Stochastic Models 14 (1998), 273–295.
- A. Polanski and M. Kimmel, *New explicit expressions for relative frequencies of single-nucleotide polymorphisms with application to statistical inference on population growth*, Genetics 165 (2003), 427–436.
