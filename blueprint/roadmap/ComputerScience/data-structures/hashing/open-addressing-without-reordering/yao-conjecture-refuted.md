# Refutation of Yao's worst-case conjecture

Yao's worst-case conjecture is false: for $\delta \to 0$ with $\delta \ge n^{-o(1)}$, funnel hashing is a greedy open-addressed table without reordering whose worst-case expected probe complexity is $O(\log^2 \delta^{-1}) = o(\delta^{-1})$.

## Proof sketch

Immediate from the funnel-hashing bound, since $\log^2 \delta^{-1} / \delta^{-1} \to 0$ as $\delta \to 0$, while the conjecture demands at least $(1-o(1))\delta^{-1}$.

## Depends on

- [Yao's worst-case conjecture for greedy open addressing](yao-worst-case-conjecture.md)
- [Funnel hashing layout](funnel-hashing-layout.md)
- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)

## Proof depends on

- [Funnel hashing: squared-logarithmic worst-case probes for a greedy table](funnel-hashing-bounds.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
