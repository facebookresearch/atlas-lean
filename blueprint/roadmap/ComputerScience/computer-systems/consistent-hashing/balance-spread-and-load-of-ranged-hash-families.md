# Balance, spread and load of ranged hash families

Let $\mathcal F$ be a family of [ranged hash functions](ranged-hash-functions.md) on items $\mathcal I$ and buckets $\mathcal B$.

- **Balance.** $\mathcal F$ is *balanced* if, for a fixed view $\mathcal V$ and a fixed set of items, with high probability over a randomly chosen function of $\mathcal F$ the fraction of items mapped to each bucket of $\mathcal V$ is $O(1/|\mathcal V|)$.
- **Spread.** For a collection $\mathcal V_1, \dots, \mathcal V_V$ of views, the *spread* $\sigma(i)$ of an item $i$ is the number of distinct buckets $f_{\mathcal V_j}(i)$, $1 \le j \le V$, to which it is mapped in the different views.
- **Load.** The *load* $\lambda(b)$ of a bucket $b$ is the number of distinct items assigned to $b$ in at least one of the views: $\lambda(b) = |\bigcup_j f_{\mathcal V_j}^{-1}(b)|$.

A good consistent hash family has low spread and low load whenever each view contains a constant fraction of the buckets.

## Depends on

- [Ranged hash functions](ranged-hash-functions.md)

## Sources

- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent hashing and random trees: distributed caching protocols for relieving hot spots on the World Wide Web", *Proceedings of the 29th Annual ACM Symposium on Theory of Computing*, 654–663, 1997, Section 4.1 (balance, spread and load).
