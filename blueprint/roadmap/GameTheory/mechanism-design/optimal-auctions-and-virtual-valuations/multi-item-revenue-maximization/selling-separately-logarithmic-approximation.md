# Selling separately loses at most a logarithmic factor for independent items

For a single additive buyer with independent item values on $n$ items, $\mathrm{SREV}(D) \ge \mathrm{REV}(D) / O(\log n)$, and this is tight: there are product distributions with $\mathrm{REV}(D) / \mathrm{SREV}(D) = \Omega(\log n)$. In general neither $\mathrm{SREV}$ nor $\mathrm{BREV}$ alone is a constant-factor approximation of $\mathrm{REV}$.

## Proof sketch

Decompose the buyer's value into a core, where each item's value is below a threshold at the scale of $\mathrm{SREV}$, and a tail, where some item's value is large. Revenue from the tail is charged to selling separately via a union-bound argument, while the core welfare is a sum of bounded independent variables; splitting it into dyadic value scales and selling each item at a scale-dependent price recovers a $1/O(\log n)$ fraction. Equal-revenue distributions on each item give the $\Omega(\log n)$ separation, and products of equal-revenue distributions versus independent point masses separate each simple mechanism from the optimum.

## Depends on

- [Single additive buyer with independent item values: SREV, BREV and REV](additive-buyer-srev-brev-rev.md)

## Sources

- X. Li, A. C.-C. Yao, "On revenue maximization for selling multiple independently distributed items", Proceedings of the National Academy of Sciences 110(28) (2013).
- S. Hart, N. Nisan, "Approximate revenue maximization with multiple items", Journal of Economic Theory 172 (2017); EC 2012.
