# Balance, spread and load of ranged hash families

Let $\mathcal F$ be a family of [ranged hash functions](ranged-hash-functions.md) on items $\mathcal I$ and buckets $\mathcal B$.

- **Balance.** $\mathcal F$ is *balanced* if, for a fixed view $\mathcal V$ and a fixed set of items, with high probability over a randomly chosen function of $\mathcal F$ the fraction of items mapped to each bucket of $\mathcal V$ is $O(1/|\mathcal V|)$.
- **Spread.** Let $\mathcal V_1, \dots, \mathcal V_V$ be views that together contain $C$ distinct buckets and that each contain at least $C/t$ buckets. The *spread* $\sigma(i)$ of an item $i$ is the number of distinct buckets $f_{\mathcal V_j}(i)$, $1 \le j \le V$, to which it is mapped in the different views.
- **Load.** For such views, the *load* $\lambda(b)$ of a bucket $b$ is the number of distinct items assigned to $b$ in at least one of the views: $\lambda(b) = |\bigcup_j f_{\mathcal V_j}^{-1}(b)|$.

The spread of a hash function is the largest spread of an item, and a family has spread $\sigma$ if a random function from it has spread $\sigma$ with high probability; the load of a function and of a family are defined in the same way. A good consistent hash family has low spread and low load whenever each view contains a constant fraction $1/t$ of the buckets.

## Depends on

- [Ranged hash functions](ranged-hash-functions.md)

## Sources

- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent hashing and random trees: distributed caching protocols for relieving hot spots on the World Wide Web", *Proceedings of the 29th Annual ACM Symposium on Theory of Computing*, 654–663, 1997, Section 4.1 (balance, spread and load).
