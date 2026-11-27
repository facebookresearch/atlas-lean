# Cache complexity of a k-merger

In the [ideal-cache model](the-ideal-cache-model.md) with cache size $Z$ and line length $L$, if $Z = \Omega(L^2)$ then one invocation of a [$k$-merger](k-mergers.md) incurs at most

$$
Q_M(k) = O\bigl(1 + k + k^3/L + (k^3/L)\log_Z k\bigr)
$$

cache misses. If $k < \alpha\sqrt Z$ for a suitable constant $\alpha$, the whole merger and one line per input fit in cache, giving $O(1 + k + k^3/L)$; otherwise the recurrence $Q_M(k) \le (2k^{3/2} + 2\sqrt k)\,Q_M(\sqrt k) + k^2$ applies, the $k^2$ term for checking the buffers before each of the $k^{3/2}$ invocations of the right merger.

## Depends on

- [k-mergers](k-mergers.md)

## Proof depends on

- [A k-merger fits in quadratic space](a-k-merger-fits-in-quadratic-space.md)
- [Circular queues cost one miss per line](circular-queues-cost-one-miss-per-line.md)

## Sources

- M. Frigo, C. E. Leiserson, H. Prokop and S. Ramachandran, "Cache-oblivious algorithms", *Proceedings of the 40th Annual Symposium on Foundations of Computer Science*, 1999, Section 4, Lemma 6 with its proof (the two cases and the recurrence).
