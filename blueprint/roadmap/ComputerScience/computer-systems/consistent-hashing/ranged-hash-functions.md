# Ranged hash functions

Let $\mathcal I$ be a set of items and $\mathcal B$ a set of buckets, with $I = |\mathcal I|$. A *view* is a nonempty subset $\mathcal V \subseteq \mathcal B$ of the buckets, the buckets a client knows about. A *ranged hash function* is a function $f : (2^{\mathcal B} \setminus \{\emptyset\}) \times \mathcal I \to \mathcal B$, defined on all views and items, written $f_{\mathcal V}(i) = f(\mathcal V, i)$, that assigns every item to a usable bucket of every view: $f_{\mathcal V}(i) \in \mathcal V$. A *ranged hash family* is a family of ranged hash functions, and a random ranged hash function is one drawn at random from a family.

A ranged hash function is *monotone* if for all views $\mathcal V_1 \subseteq \mathcal V_2$ and items $i$, $f_{\mathcal V_2}(i) \in \mathcal V_1$ implies $f_{\mathcal V_1}(i) = f_{\mathcal V_2}(i)$: when buckets are added to a view, items move only to the new buckets. A *$\pi$-hash function* is a ranged hash function given by a permutation $\pi(i)$ of $\mathcal B$ for each item $i$ (not necessarily chosen uniformly or independently), with $f_{\mathcal V}(i)$ the first bucket of $\pi(i)$ that lies in $\mathcal V$.

## Sources

- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent hashing and random trees: distributed caching protocols for relieving hot spots on the World Wide Web", *Proceedings of the 29th Annual ACM Symposium on Theory of Computing*, 654–663, 1997, Section 4.1 (views, ranged hash functions and families, monotonicity) and Section 4.4 ($\pi$-hash functions).
