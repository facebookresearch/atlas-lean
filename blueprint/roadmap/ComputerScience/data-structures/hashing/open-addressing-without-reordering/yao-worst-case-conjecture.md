# Yao's worst-case conjecture for greedy open addressing

*Yao's conjecture* (1985, Section 4) asserts that, for every fixed load factor $0 < \alpha < 1$, every greedy open-addressed hash table without reordering has worst-case expected probe complexity at least $\frac{1}{1-\alpha} - o(1)$ as $n \to \infty$, that is, at least $(1 - o(1))\,\delta^{-1}$ when filled to $n - \delta n$ keys with $\delta = 1 - \alpha$ fixed: uniform probing would be asymptotically optimal also for the cost of the most expensive insertion, whose last insertion costs $\frac{n+1}{\delta n + 2} \to \delta^{-1}$. Farach-Colton, Krapivin and Kuszmaul restate it as the bound $(1 - o(1))\,\delta^{-1}$. In Yao's form the $o(1)$ is taken as $n \to \infty$ with $\delta$ fixed; this differs from a high-load limit $\delta \to 0$ with $\delta n \to \infty$, although uniform probing also costs $(1 + o(1))\,\delta^{-1}$ there. Funnel hashing, a greedy table, refutes the fixed-$\delta$ form: its worst-case expected probe complexity $O(\log^2 \delta^{-1})$, with a constant independent of $\delta$, is below $\frac{1}{2}\delta^{-1}$ for every fixed $\delta$ below some absolute constant.

## Depends on

- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)

## Sources

- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
