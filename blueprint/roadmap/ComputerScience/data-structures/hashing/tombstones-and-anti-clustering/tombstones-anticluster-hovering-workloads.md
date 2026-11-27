# Tombstones defeat primary clustering under hovering workloads

Consider ordered linear probing with tombstones and uniformly random hashing, with operations oblivious to the hash function.

1. With the classical rebuild window $R = n/(2x)$ insertions and a hovering workload at load factor $1 - 1/x$, the expected amortized time per insertion is $\tilde{O}(x^{1.5})$; if all insertions and deletions are on distinct keys it is $\Omega(x^{1.5}\sqrt{\lg\lg x})$; queries take expected time $O(x)$ (Theorem 1).
2. With rebuild window $R = n/\lg^{c} x$ insertions for a sufficiently large constant $c$, and any sequence of operations that never brings the load factor above $1 - 1/x$, the expected amortized cost of each insertion is $\tilde{O}(x)$ and the expected cost of each query or deletion is $O(x)$ (Theorem 2). For every choice of $R$ some sequence of operations takes amortized time $\omega(x)$ per operation.

Both beat insertion-only linear probing at the same load factor $\alpha = 1 - 1/x$, whose expected insertion (unsuccessful-search) cost tends to $\frac12(1 + x^2) = \Theta(x^2)$, while its expected successful-search cost tends to $\frac12(1 + x)$.

## Proof sketch

Deletions leave tombstones at hash-random positions that later insertions reuse. The cost of an insertion $u$ is governed by its displacement $d_u$, and $\sum_u d_u = \sum_j c_j$, where the *crossing number* $c_j$ counts the insertions of the rebuild window with hash below $j$ whose run reaches past $j$; for a window of $R$ insertions this gives $\mathbb{E}[d_u] = \Theta((n/R)\,\mathbb{E}[c_j])$. Bounding $c_j$ reduces to the largest deviation between the numbers of insertions and deletions along monotone paths in a grid; with $R = n/(2x)$ this deviation is $\tilde{O}(\sqrt{x})$, giving $\tilde{O}(x^{1.5})$, and with $R = n/\mathrm{polylog}(x)$ it gives $\mathbb{E}[c_j] = O(x)$, hence $O(x)$ queries and $\tilde{O}(x)$ insertions. Rebuilds cost $\Theta(n)$ each.

## Depends on

- [Ordered linear probing](ordered-linear-probing.md)
- [Linear probing with tombstones and periodic rebuilds](linear-probing-with-tombstones.md)

## Proof depends on

- [Expected cost of an unsuccessful linear-probing search at a fixed load factor](../analysis-of-linear-probing/tendsto-insertion-cost.md)
- [Expected cost of a successful linear-probing search at a fixed load factor](../analysis-of-linear-probing/tendsto-successful-search-cost.md)

## Sources

- Michael A. Bender, Bradley C. Kuszmaul, William Kuszmaul, "Linear Probing Revisited: Tombstones Mark the Demise of Primary Clustering", FOCS (2021), arXiv:2107.01250.
