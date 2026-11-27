# Run-length encoding of order-preserving k-mer weights

**Setting.** Let $K$ be a set of $n$ distinct $k$-mers, each with a weight $w(g)$ (for example its abundance), stored as a spectrum-preserving string set $S = \{S_1, \dots, S_m\}$ in which every $k$-mer of $K$ occurs exactly once. An order-preserving $k$-mer dictionary implements $h : \Sigma^k \to \{0, 1, \dots, n\}$ with $h(g) = 0$ for $g \notin K$ and such that consecutive $k$-mers of a string (overlapping on $k-1$ symbols) receive consecutive codes $h(g_2) = h(g_1) + 1$. Ordering the strings fixes the sequence of weights $W[1..n]$ with $W[h(g)] = w(g)$.

**Encoding.** Write $W$ as $r$ maximal runs $\langle w_1, \ell_1 \rangle \cdots \langle w_r, \ell_r \rangle$ with $w_i \ne w_{i+1}$ and $\sum_i \ell_i = n$. Store the set $D$ of distinct weights with $|D| \lceil \log_2 \max \rceil$ bits, each run value as an index into $D$, and the prefix sums of $0, \ell_1, \dots, \ell_{r-1}$ with Elias-Fano coding. The weights then take at most

$$r \Big( \lceil \log_2 |D| \rceil + \Big\lceil \log_2 \frac{n}{r} \Big\rceil + 2 + o(1) \Big) + |D| \lceil \log_2 \max \rceil \ \text{bits}$$

on top of the dictionary, proportional to the number of runs rather than to $n$, and $w(g)$ is retrieved from $h(g)$ by one predecessor query in $O(\log(n/r))$ time.

**Reducing runs.** Without cutting strings, the only freedom is the order and orientation (reverse complement, which reverses the weight sequence of a string) of the $m$ strings. If string $S_i$ has $r_i$ internal runs and $R = \sum_i r_i$, then for any arrangement corresponding to a path cover $C$ of the end-point weight graph (strings glued when the last weight of one equals the first weight of the next) the number of runs is

$$r = R - m + |C|,$$

so minimizing runs is equivalent to finding a minimum-cardinality path cover.

## Proof depends on

- [Succinct rank and select](../../../../ComputerScience/data-structures/range-query-structures/advanced-data-structures/succinct-rank-and-select.md)

## Expansion

Order preservation is what makes the weights compressible: neighbouring $k$-mers on a genome usually have equal abundance, so $W$ has long runs, whereas a minimal perfect hash function scatters $k$-mers and destroys runs. Each path of the cover starts a fresh run at its first string, and every junction inside a path glues two runs into one, which yields $r = R - m + |C|$ since a cover of $m$ nodes by $|C|$ paths has $m - |C|$ junctions.

## Sources

- G. E. Pibiri, "On weighted k-mer dictionaries", Algorithms for Molecular Biology 18 (2023) 3, sections on representing runs of weights and computing a minimum-size path cover (Definitions 1-3, Lemmas 1-5, Theorem 1), <https://doi.org/10.1186/s13015-023-00226-2> (PMC10276434).
