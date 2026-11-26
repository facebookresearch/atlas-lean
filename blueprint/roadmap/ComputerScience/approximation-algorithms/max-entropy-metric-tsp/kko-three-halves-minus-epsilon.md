# Karlin-Klein-Oveis Gharan: max-entropy rounding beats 3/2 for metric TSP

There is an absolute constant $\epsilon > 10^{-36}$ such that for every metric TSP instance $(V,c)$ the max-entropy rounding algorithm runs in randomized polynomial time and outputs a Hamiltonian cycle $H$ with

$$
\mathbb{E}[c(H)] \le \Big(\frac32-\epsilon\Big)\,\mathrm{OPT}.
$$

Thus metric TSP has a randomized $(\tfrac32-10^{-36})$-approximation algorithm in expectation, the first improvement over the Christofides-Serdyukov factor $\tfrac32$. Combined with the reduction of Traub, Vygen and Zenklusen, metric path TSP also admits a randomized $(\tfrac32-\epsilon')$-approximation for some absolute $\epsilon' > 0$.

## Proof sketch

Write the cost of the parity correction as the cost of a fractional point $y$ in the $O$-join dominant and construct $y=\tfrac{x}{2}-$ (reductions on good edges) $+$ (payments on near minimum cuts that become even in $T$). Near minimum cuts are organized into a laminar hierarchy of degree cuts and polygon cuts using the one-sided polygon structure. For strongly Rayleigh $\mu_\lambda$, each good edge has its two endpoint cuts simultaneously even with constant probability by the joint count bound and negative dependence, so the expected reduction exceeds the expected payment by $\epsilon\,\mathrm{OPT}$. Wolsey's bound handles the tree part.

## Depends on

- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Wolsey's bound: tree plus minimum T-join costs at most 3/2 of the subtour LP](wolsey-three-halves-subtour.md)
- [Lambda-uniform spanning tree measures are strongly Rayleigh](lambda-uniform-trees-strongly-rayleigh.md)
- [Negative dependence and Poisson-binomial counts under strongly Rayleigh measures](strongly-rayleigh-negative-dependence.md)
- [Joint count probabilities for strongly Rayleigh measures (Karlin-Klein-Oveis Gharan)](sr-joint-count-bound.md)
- [Polygons of near-minimum cuts crossed on one side (Karlin-Klein-Oveis Gharan)](one-sided-polygon-structure.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Wolsey's bound: tree plus minimum T-join costs at most 3/2 of the subtour LP](wolsey-three-halves-subtour.md)
- [Lambda-uniform spanning tree measures are strongly Rayleigh](lambda-uniform-trees-strongly-rayleigh.md)
- [Negative dependence and Poisson-binomial counts under strongly Rayleigh measures](strongly-rayleigh-negative-dependence.md)
- [Joint count probabilities for strongly Rayleigh measures (Karlin-Klein-Oveis Gharan)](sr-joint-count-bound.md)
- [Polygons of near-minimum cuts crossed on one side (Karlin-Klein-Oveis Gharan)](one-sided-polygon-structure.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409.
