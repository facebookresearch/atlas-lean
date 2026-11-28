# False discoveries of a bit-sliced Bloom filter index

**Index.** Let $N$ datasets each be summarized by a Bloom filter of length $m$ bits built with the same $\eta$ hash functions $h_1, \dots, h_\eta : \Sigma^k \to \{1, \dots, m\}$ applied to the dataset's set of distinct $k$-mers (at most $K_{\max}$ of them). Concatenating the filters as columns gives an $m \times N$ bit matrix $B$. A $k$-mer $x$ is reported present in dataset $j$ iff

$$\bigwedge_{t=1}^{\eta} B_{h_t(x),\, j} = 1 ,$$

that is, column $j$ of the bitwise AND of the $\eta$ rows $h_1(x), \dots, h_\eta(x)$. A query sequence with $L$ distinct $k$-mers is reported present in dataset $j$ when all $L$ of its $k$-mers are reported present (or, for approximate search, when a chosen fraction of them are). Bloom filters have no false negatives, so every dataset that truly contains all query $k$-mers is returned.

**False discoveries.** Let $p$ be the false positive rate of a single filter for a single absent $k$-mer, and assume that false positives are independent across $k$-mers and datasets. Then the expected number $V$ of datasets falsely reported to contain an exact query with $L$ distinct $k$-mers, none of which they contain, satisfies

$$q := \mathbb{E}[V] \le N p^{L} .$$

**Parameter choice.** To guarantee $q \le q_{\max}$ for all queries with at least $L_{\min}$ distinct $k$-mers it suffices that $N p^{L_{\min}} = q_{\max}$, i.e.

$$p = \left(\frac{q_{\max}}{N}\right)^{1/L_{\min}} .$$

With the standard Bloom filter optimum for $n = K_{\max}$ inserted elements, $m = -n \ln p / (\ln 2)^2$ and $\eta = -\ln p / \ln 2$, this gives

$$m = -\frac{K_{\max}\, \ln(q_{\max}/N)}{L_{\min} (\ln 2)^2}, \qquad \eta = -\frac{\ln(q_{\max}/N)}{L_{\min} \ln 2} .$$

## Depends on

- [Bloom filter](../../../../ComputerScience/data-structures/hashing/bloom-filter/bloom-filter.md)
- [Exponential approximation of the Bloom filter false-positive rate](../../../../ComputerScience/data-structures/hashing/bloom-filter/exp-approx.md)
- [The optimal number of hash functions](../../../../ComputerScience/data-structures/hashing/bloom-filter/exp-approx-optimal.md)
- [Exponential approximation at the optimal number of hash functions](../../../../ComputerScience/data-structures/hashing/bloom-filter/exp-approx-at-optimum.md)

## Expansion

The bound $N p^L$ is a union over datasets of the event that all $L$ independent single-$k$-mer tests fail; it is an upper bound because a filter holding fewer than $K_{\max}$ elements has a smaller false positive rate. Because the exponent is the number of query $k$-mers, a false positive rate as large as $p \approx 0.25$ per lookup still yields negligible false discoveries for a $31$-mer query of moderate length, which is what allows a small $\eta$ and a compact matrix. Two caveats limit the model: datasets from closely related genomes have correlated filters, so false positives are not independent across columns; and any path through a genome's de Bruijn graph whose $k$-mers all occur in the genome (possible when the query contains repeated $k$-mers) is reported present although it is not a substring of the genome. Adding a dataset appends a column, so the index grows incrementally without rebuilding.

## Sources

- P. Bradley, H. C. den Bakker, E. P. C. Rocha, G. McVean, Z. Iqbal, "Ultrafast search of all deposited bacterial and viral genomic data", Nature Biotechnology 37 (2019) 152–159, Online Methods, sections "BIGSI construction" and "Parameter choices", <https://doi.org/10.1038/s41587-018-0010-1> (PMC6420049).
