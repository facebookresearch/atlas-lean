# Union Bloom filter size and optimal hash count

**Bloom filter.** A Bloom filter with $m$ bits and $h$ independent uniform hash functions storing $N$ items has false-positive rate $(1 - e^{-hN/m})^h$, minimized at $h = (m/N)\ln 2$, where it equals $(1/2)^h$.

**Overlap model.** Let $S = \{S_1,\dots,S_r\}$ be $r$ sequencing experiments, each containing $n$ distinct $k$-mers, and suppose each $k$-mer of $S_i$ is absent from each earlier experiment $S_j$ ($j<i$) independently with probability $1-p$, where $p \in (0,1]$ is the overlap probability.

**Lemma 1.** The expected number of distinct $k$-mers in the union $U = \bigcup_{i=1}^r S_i$ is

$$\mathbb{E}[|U|] = \sum_{i=1}^{r} n(1-p)^{i-1} = \frac{n\,(1-(1-p)^r)}{p}.$$

**Theorem 1.** For a union filter of $m$ bits holding $U$ with its expected number of elements, the number of hash functions minimizing the false-positive rate is

$$h^* = \frac{m\ln 2}{n(1-(1-p)^r)/p} = \frac{p\ln 2}{(1-(1-p)^r)\,\mathrm{load}}, \qquad \mathrm{load} = n/m,$$

and the resulting false-positive rate is $(1/2)^{h^*}$, which is at most $1/2$ whenever $h^* \ge 1$.

## Depends on

- [Bloom filter](../../../../ComputerScience/data-structures/hashing/bloom-filter/bloom-filter.md)
- [Exponential approximation of the Bloom filter false-positive rate](../../../../ComputerScience/data-structures/hashing/bloom-filter/exp-approx.md)
- [The optimal number of hash functions](../../../../ComputerScience/data-structures/hashing/bloom-filter/exp-approx-optimal.md)

## Expansion

$\mathbb{E}[|U|] = \mathbb{E}|S_1| + \mathbb{E}|S_2 \setminus S_1| + \cdots$, and a $k$-mer of $S_i$ is new to $\bigcup_{j<i} S_j$ with probability $(1-p)^{i-1}$, giving the geometric sum. Theorem 1 then applies the classical Bloom-filter optimum to a single filter containing $n(1-(1-p)^r)/p$ items. As $p \to 1$ the union has about as many elements as one experiment, so every node of the tree can use a filter of the same size; in practice the size is set from an estimate of the total number of distinct $k$-mers.

## Sources

- B. Solomon, C. Kingsford, "Fast search of thousands of short-read sequencing experiments", Nature Biotechnology 34(3) (2016) 300–302, Online Methods, Lemma 1, Theorem 1, Eqs. (1)–(3), <https://doi.org/10.1038/nbt.3442>, PMCID PMC4804353.
