# Monotonicity of nearest-point consistent hashing

Let the set $\mathcal B$ of buckets be finite, let $r_{\mathcal B}$ map each bucket $b$ to a nonempty finite set of points $r_{\mathcal B}(b) \subseteq [0, 1]$ (its replicas) and $r_{\mathcal I}$ map each item to a point $r_{\mathcal I}(i) \in [0, 1]$, all points being distinct. Define the ranged hash function $f_{\mathcal V}(i)$ to be the bucket $b \in \mathcal V$ owning the point of $\bigcup_{b \in \mathcal V} r_{\mathcal B}(b)$ nearest to $r_{\mathcal I}(i)$, ties at equal distance broken by a fixed order of the points. Since every view is a nonempty set of buckets and each bucket has at least one replica, the union is a nonempty finite set and the nearest point exists. Then $f$ is a monotone [ranged hash function](ranged-hash-functions.md): when buckets are added to a view, the only items that move are those whose nearest point now belongs to a new bucket, and no item moves between old buckets.

## Depends on

- [Ranged hash functions](ranged-hash-functions.md)

## Sources

- D. Karger, E. Lehman, T. Leighton, R. Panigrahy, M. Levine and D. Lewin, "Consistent hashing and random trees: distributed caching protocols for relieving hot spots on the World Wide Web", *Proceedings of the 29th Annual ACM Symposium on Theory of Computing*, 654–663, 1997, Section 4.2 (the construction: each bucket replicated and mapped to the unit interval, each item mapped to the bucket "closest" to it) and Theorem 4.1, property 1, with the first sentence of its proof sketch.
