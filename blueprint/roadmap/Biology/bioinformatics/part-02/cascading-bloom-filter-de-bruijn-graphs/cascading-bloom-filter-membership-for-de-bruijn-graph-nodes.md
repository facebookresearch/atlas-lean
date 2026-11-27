# Cascading Bloom filter membership for de Bruijn graph nodes

Let $T_0$ be the set of $k$-mers (nodes) of a de Bruijn graph, $|T_0| = N$, and assume queries are made only for elements of $T_0$ or their potential neighbours (the eight one-letter extensions of a node), as in graph traversal. Build Bloom filters recursively: $B_1$ stores $T_0$, and $T_1$ is the set of **critical false positives**, potential neighbours of $T_0$ that are accepted by $B_1$ but are not in $T_0$; for $i \ge 2$, $B_i$ stores $T_{i-1}$ and $T_i$ is the set of elements of $T_{i-2}$ accepted by $B_i$ by mistake. Thus $T_i \subseteq T_0$ for even $i$ and $T_i \subseteq T_1$ for odd $i$.

**Lemma (correctness).** For a queried $k$-mer $u$, let $i$ be the smallest index with $u \notin B_{i+1}$ ($i = 0$ if $u \notin B_1$). Then $u \in T_0$ if $i$ is odd and $u \notin T_0$ if $i$ is even. If the cascade is truncated after $t$ filters and $u$ passes all of them, membership is decided by an explicit lookup in $T_t$.

**Memory.** If each filter uses $r$ bits per stored element and has false-positive rate $c^r$ with $c \approx 0.6185$ (optimal number of hash functions), and each node has on average six non-node extensions, the expected number of bits per $k$-mer for an infinite cascade is

$$r + 6 r c^r + r c^r + 6 r c^{2r} + \cdots = \frac{(1 + 6c^r)\, r}{1 - c^r},$$

minimized at $r \approx 5.464$, giving about $8.45$ bits per $k$-mer, independent of $k$. Allowing a different ratio $r_i$ per filter lowers the optimum to about $7.93$ bits (at $r_1 \approx 4.41$, $r_i \approx 1.44$ for $i > 1$).

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)
- [Bloom filter](../../../../ComputerScience/data-structures/hashing/bloom-filter/bloom-filter.md)

## Expansion

Bloom filters have one-sided error: $u \notin B_{i+1}$ implies $u \notin T_i$. Membership in $B_1 \cap \dots \cap B_i$ implies $u \in T_{i-1} \cup T_i$ by induction, so the first failing filter places $u$ in $T_{i-1}$, whose parity says whether it is a true node or a false positive. Because each $|T_i|$ shrinks geometrically, the cascade costs a constant factor over a single filter in construction time, while replacing the large explicit table of critical false positives of the single-filter scheme by a tiny final table; four filters already come within a few percent of the infinite-cascade optimum.

## Sources

- K. Salikhov, G. Sacomoto and G. Kucherov, "Using cascading Bloom filters to improve the memory usage for de Brujin graphs", Algorithms for Molecular Biology 9 (2014), 2, Lemma 1, Eqs. (3)–(4), Tables 1–2, <https://doi.org/10.1186/1748-7188-9-2>, PMCID: PMC3974045.
- R. Chikhi and G. Rizk, "Space-efficient and exact de Bruijn graph representation based on a Bloom filter", Algorithms for Molecular Biology 8 (2013), 22, <https://doi.org/10.1186/1748-7188-8-22>.
