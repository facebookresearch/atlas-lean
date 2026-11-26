# Yao's theorem: uniform hashing is amortized-optimal among greedy tables

For every fixed load $\alpha = 1 - \delta \in (0, 1)$ and every greedy open-addressed hash table without reordering, the amortized expected probe complexity after $\lfloor \alpha n \rfloor$ insertions into an array of $n$ slots is at least $(1 - o(1))\,\alpha^{-1}\ln (1-\alpha)^{-1}$ as $n \to \infty$, which is the asymptotic cost of uniform probing. In particular every greedy table has amortized expected probe complexity $\Omega(\log \delta^{-1})$; this confirms Ullman's 1972 conjecture.

## Proof sketch

For a greedy scheme the probe complexity of a key equals the number of probes needed to reach a free slot, so the total cost is determined by the occupancy process. Yao shows that, among all probe distributions, the expected number of occupied slots seen before a free one is minimized in aggregate when every probe sequence is a uniform permutation, by an exchange argument that symmetrizes the distribution of the first probes and a convexity bound on the resulting occupancy recursion. The resulting recursion matches the uniform-probing integral $\alpha^{-1}\int_0^{\alpha}(1-t)^{-1}\,dt$.

## Depends on

- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)

## Proof depends on

- [Exact expected probe complexity of uniform probing](exact-cost-of-uniform-probing.md)

## Sources

- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
- Jeffrey D. Ullman, "A Note on the Efficiency of Hashing Functions", Journal of the ACM 19(3) (1972).
- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
