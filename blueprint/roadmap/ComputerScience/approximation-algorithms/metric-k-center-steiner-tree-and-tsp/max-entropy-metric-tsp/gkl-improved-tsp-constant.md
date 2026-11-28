# Gurvits-Klein-Leake: metric TSP has a randomized (3/2 - 10^{-34})-approximation

There is a randomized polynomial-time algorithm for metric TSP whose output tour $H$ satisfies $\mathbb{E}[c(H)] \le (\tfrac32-\epsilon)\,\mathrm{OPT}$ for an absolute constant $\epsilon > 10^{-34}$. The algorithm is max-entropy rounding; the improvement comes from replacing the doubly exponential joint count bound by the simply exponential one in the analysis.

## Proof sketch

Every probabilistic estimate in the Karlin-Klein-Oveis Gharan analysis that depends only on expectations of block counts is replaced by the simply exponential bound. The remaining two bottleneck estimates, not determined by expectations alone, are sharpened separately. Re-optimizing the constants yields about a hundredfold improvement of $\epsilon$.

## Depends on

- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Simply exponential joint count bound for strongly Rayleigh measures (Gurvits-Klein-Leake)](gkl-simply-exponential-bound.md)
- [Karlin-Klein-Oveis Gharan: max-entropy rounding beats 3/2 for metric TSP](kko-three-halves-minus-epsilon.md)

## Sources

- Leonid Gurvits, Nathan Klein, Jonathan Leake, "From Trees to Polynomials and Back Again: New Capacity Bounds with Applications to TSP", ICALP (2024), arXiv:2311.09072.
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409.
