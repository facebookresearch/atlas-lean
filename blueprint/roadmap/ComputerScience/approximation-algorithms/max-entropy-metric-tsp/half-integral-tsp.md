# Metric TSP with a half-integral subtour LP optimum is 1.49993-approximable

Call a metric TSP instance half-integral if its subtour elimination LP has an optimal solution $x$ with $x_e \in \{0,\tfrac12,1\}$ for every edge $e$. There is a randomized polynomial-time algorithm that, on every half-integral instance, outputs a tour of expected cost at most $1.49993\cdot\mathrm{OPT}$. Half-integral instances are conjectured (Schalekamp, Williamson and van Zuylen) to attain the integrality gap of the subtour LP.

## Proof sketch

On a half-integral point every vertex has $x(\delta(v))=2$ with half-edges, and the minimum cuts of value 2 form a cactus-like laminar hierarchy of degree cuts and cycle cuts. Sample a max-entropy spanning tree and show that a constant fraction of the edges are good: both endpoint cuts are even with constant probability, by negative dependence of the strongly Rayleigh measure. Reducing $x/2$ on good edges while paying on odd cuts lowers the expected parity correction below $\tfrac12\mathrm{OPT}_{\mathrm{LP}}$ by a fixed amount.

## Depends on

- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Subtour elimination LP of a metric TSP instance](subtour-elimination-lp.md)
- [Negative dependence and Poisson-binomial counts under strongly Rayleigh measures](strongly-rayleigh-negative-dependence.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Negative dependence and Poisson-binomial counts under strongly Rayleigh measures](strongly-rayleigh-negative-dependence.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "An Improved Approximation Algorithm for TSP in the Half Integral Case", STOC (2020), arXiv:1908.00227.
