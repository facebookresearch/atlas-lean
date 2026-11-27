# Elastic hashing: constant amortized and logarithmic worst-case probe complexity

Let $n \in \mathbb{N}$ and $\delta \in (0, 1)$ with $\delta \ge C/n$ for a suitable constant $C$ and $\delta^{-1}$ a power of two. Elastic hashing supports $n - \delta n$ insertions into an array of $n$ slots without reordering, with amortized expected probe complexity $O(1)$, worst-case expected probe complexity $O(\log \delta^{-1})$, and worst-case expected insertion time $O(\log \delta^{-1})$.

## Proof sketch

Keys placed in $A_i$ while its free fraction is $\varepsilon$ succeed within $O(\varepsilon^{-1})$ expected probes or overflow to $A_{i+1}$, whose free fraction stays above $1/4$; the cap $f(\varepsilon)$ prevents expensive placements from ever being charged more than $O(\min(\log^2 \varepsilon^{-1}, \log \delta^{-1}))$ inner probes. Summing $\varepsilon^{-1}$ over the geometric fill schedule of each $A_i$ gives $O(1)$ amortized probes per key in subarray coordinates, and the injection of cost $O(i j^2)$ converts these into one-dimensional probe indices with only constant amortized loss because subarray sizes halve. The worst case is dominated by keys that try $c \log \delta^{-1}$ probes in a nearly full $A_i$.

## Depends on

- [Elastic hashing layout and batch insertion rule](elastic-hashing-layout.md)
- [Amortized, worst-case and high-probability probe complexity](amortized-and-worst-case-probe-complexity.md)
- [Open-addressing insertion without reordering](oa-without-reordering-model.md)

## Proof depends on

- [Failure probability of a bounded number of uniform probes](bounded-probe-failure.md)
- [An injection of index pairs with cost $O(i j^2)$](pairing-injection-with-quadratic-weight.md)

## Sources

- Martín Farach-Colton, Andrew Krapivin, William Kuszmaul, "Optimal Bounds for Open Addressing Without Reordering", FOCS (2024), arXiv:2501.02305.
