# Deterministic flow rounding without increasing the cost

There is a deterministic algorithm that, given a feasible fractional flow $\mathbf{f}$ for an $m$-edge, $n$-vertex minimum-cost flow instance with integral demands and integral capacities, outputs a feasible integral flow $\mathbf{f}'$ with $\mathbf{c}^{\top}\mathbf{f}' \le \mathbf{c}^{\top}\mathbf{f}$ in $O(m\log m)$ time. In particular, a fractional feasible flow of cost less than $F^* + 1/2$ for an instance with integral costs rounds to an exact minimum-cost flow.

## Proof sketch

Consider the fractional parts of $\mathbf{f}$; they form a circulation plus integral corrections, and the edges with nonintegral flow support cycles. Repeatedly find such a cycle using dynamic trees and push flow around it in the direction that does not increase cost until some edge becomes integral; bit-scaling over the binary expansion of the fractional parts lets each phase be implemented in near-linear total time. The last claim follows since an integral feasible flow has integral cost at least $F^*$ and at most $\mathbf{c}^{\top}\mathbf{f} < F^* + 1/2$.

## Depends on

- [Integral minimum-cost flow instances with polynomially bounded data](integral-min-cost-flow-instance.md)

## Proof depends on

- [Link-cut trees take logarithmic amortized time](../../../../data-structures/disjoint-sets-and-dynamic-trees/link-cut-tree/link-cut-trees-take-logarithmic-amortized-time.md)

## Sources

- Donggu Kang, James Payor, "Flow Rounding", arXiv preprint (2015), arXiv:1507.08139.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
