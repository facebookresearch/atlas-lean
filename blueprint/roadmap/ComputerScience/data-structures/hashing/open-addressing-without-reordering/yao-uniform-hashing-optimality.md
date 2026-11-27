# Yao's theorem: uniform hashing is amortized-optimal among greedy tables

In Yao's model a hashing function is a probability distribution on permutations of the $n$ slots, keys draw independent permutations, and each key is inserted greedily. For every $\varepsilon > 0$ there is a constant $a_\varepsilon$ such that for all $N$ and $n$ with load $\alpha = N/n \in (\varepsilon, 1 - \varepsilon)$ and every hashing function, the expected cost of retrieving a random one of $N$ inserted keys is at least $\alpha^{-1}\ln (1-\alpha)^{-1} - o(1)$, with the error term depending only on $\varepsilon$ and $n$ (Main Theorem); this is the asymptotic cost of uniform probing. For a full table ($N = n$) the cost is at least $\ln n - \ln\ln n - b$ for an absolute constant $b$. This confirms Ullman's 1972 conjecture in the asymptotic sense. Farach-Colton, Krapivin and Kuszmaul use the consequence that every greedy table filled to load $1 - \delta$ has amortized expected probe complexity $\Omega(\log \delta^{-1})$ (their Proposition 7).

## Proof sketch

For a greedy scheme the probe complexity of a key equals the number of probes needed to reach a free slot, so the total cost is determined by the occupancy process. Yao adapts the approach that Ajtai, Komlós and Szemerédi developed to prove Knuth's weaker conjecture for single hashing. The target value is the uniform-probing average $\frac{n+1}{N}(H_{n+1} - H_{n-N+1})$, which tends to $\alpha^{-1}\int_0^{\alpha}(1-t)^{-1}\,dt = \alpha^{-1}\ln(1-\alpha)^{-1}$.

## Depends on

- [Greedy open addressing and uniform probing](greedy-open-addressing-and-uniform-probing.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)

## Proof depends on

- [Exact expected probe complexity of uniform probing](exact-cost-of-uniform-probing.md)

## Sources

- Andrew C. Yao, "Uniform Hashing Is Optimal", Journal of the ACM 32(3) (1985).
- Jeffrey D. Ullman, "A Note on the Efficiency of Hashing Functions", Journal of the ACM 19(3) (1972).
- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
