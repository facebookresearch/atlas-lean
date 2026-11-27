# Logarithmic lower bound for worst-case probes without reordering

In the high-load regime $1/n \le \delta \le 1/2$ with $\delta n$ an integer, every open-addressed hash table without reordering (greedy or not) that performs $n - \delta n$ insertions into an array of $n$ slots has worst-case expected probe complexity $\Omega(\log \delta^{-1})$. Hence elastic hashing is optimal for both amortized and worst-case expected probe complexity.

## Proof sketch

Consider the last $\Theta(\delta n)$ insertions, made when only $O(\delta n)$ slots remain free. A key whose probe complexity is at most $t$ must find a free slot among its first $t$ probes, and the positions touched by first-$t$ probes of all keys can cover the free region only if $t$ grows with the ratio between occupied and free slots at the various stages of the fill. An averaging argument over the dyadic stages of free space, from free fraction $1/2$ down to $\delta$, forces some key's expected probe index to be $\Omega(\log \delta^{-1})$.

## Depends on

- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Open-addressing insertion without reordering](oa-without-reordering-model.md)
- [Elastic hashing layout and batch insertion rule](elastic-hashing-layout.md)

## Proof depends on

- [Elastic hashing: constant amortized and logarithmic worst-case probe complexity](elastic-hashing-bounds.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
