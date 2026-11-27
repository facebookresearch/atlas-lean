# Squared-logarithmic lower bound for greedy worst-case probes

Let $1/n \le \delta \le 1/2$ with $\delta n$ an integer, so in particular $1 - \delta = \Omega(1)$ as the source's greedy lower bound assumes. Every greedy open-addressed hash table without reordering filled to $n - \delta n$ keys has worst-case expected probe complexity $\Omega(\log^2 \delta^{-1})$, so funnel hashing is optimal among greedy tables. Furthermore, for every open-addressed table without reordering (greedy or not), the high-probability worst-case probe complexity is $\Omega(\log^2 \delta^{-1} + \log \log n)$, matching the high-probability bound of funnel hashing.

## Proof sketch

For greedy tables the probe complexity equals the number of occupied probes before the first free one, so the probe distribution must make the occupied fraction seen by early probes small at every stage of the fill. Splitting the fill into $\Theta(\log \delta^{-1})$ dyadic stages, each stage forces $\Omega(\log \delta^{-1})$ additional expected probes for late keys, giving the squared bound. The $\log \log n$ term follows from a balls-into-bins argument on the last insertions: with polynomially many keys some key sees $\Omega(\log\log n)$ consecutive collisions with high probability.

## Depends on

- [Open-addressing insertion without reordering](oa-without-reordering-model.md)
- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Funnel hashing layout](funnel-hashing-layout.md)

## Proof depends on

- [Funnel hashing: squared-logarithmic worst-case probes for a greedy table](funnel-hashing-bounds.md)
- [Maximum load of balls into bins](../../../randomized-algorithms/maximum-load-of-balls-into-bins.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
