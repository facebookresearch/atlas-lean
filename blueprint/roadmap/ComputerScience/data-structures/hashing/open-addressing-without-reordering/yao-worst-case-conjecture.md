# Yao's worst-case conjecture for greedy open addressing

*Yao's conjecture* (1985) asserts that every greedy open-addressed hash table without reordering has worst-case expected probe complexity at least $(1 - o(1))\,\delta^{-1}$ when filled to $n - \lfloor \delta n \rfloor$ keys, that is, that uniform probing is asymptotically optimal also for the cost of the most expensive insertion. The conjecture is a hypothesis about all probe distributions $P$, quantified over $n \to \infty$ and $\delta \to 0$; it is refuted by funnel hashing.

## Depends on

- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)

## Sources

- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
