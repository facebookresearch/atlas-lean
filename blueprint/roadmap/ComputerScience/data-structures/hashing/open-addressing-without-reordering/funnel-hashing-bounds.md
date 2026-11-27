# Funnel hashing: squared-logarithmic worst-case probes for a greedy table

Let $n \in \mathbb{N}$ and $\delta \in (0, 1/2]$ with $\delta n$ an integer and $\delta \ge n^{-o(1)}$. Funnel hashing is a greedy open-addressing strategy that supports $n - \delta n$ insertions into an array of $n$ slots with worst-case expected probe complexity and insertion time $O(\log^2 \delta^{-1})$. Moreover, with probability $1 - 1/\mathrm{poly}(n)$, every key in the table has probe complexity $O(\log^2 \delta^{-1} + \log\log n)$.

## Proof sketch

A key reaches level $i+1$ only if its bucket in level $i$ is full; since bucket loads in a level concentrate around the level's fill fraction and the levels shrink geometrically, the number of levels a key passes through has a geometric tail, each level costing at most $\beta = O(\log\delta^{-1})$ probes. With $\alpha = \Theta(\log\delta^{-1})$ levels the worst case is $O(\alpha\beta) = O(\log^2 \delta^{-1})$ probes, and the keys reaching the overflow array are few enough that two-choice probing there costs $O(\log \log n)$ with high probability.

## Depends on

- [Funnel hashing layout](funnel-hashing-layout.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
