# The method of conditional expectations on finite product spaces

Let $\Omega = \prod_{i=1}^{n} A_i$ be a finite product space with a product probability measure $\mu = \bigotimes_i \mu_i$, and let $f : \Omega \to \mathbb{R}$. Fixing the coordinates one at a time, each to a value maximizing the conditional expectation of $f$ given the coordinates fixed so far, yields a point $x \in \Omega$ with $f(x) \ge \mathbb{E}_\mu[f]$. If the conditional expectations are computable in polynomial time, so is $x$.

## Proof sketch

The conditional expectation given a prefix is an average of the conditional expectations of its one-coordinate extensions, so the maximizing extension never decreases it.

## Depends on

- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Sources

- N. Alon and J. H. Spencer, "The Probabilistic Method", 4th ed., Wiley, 2016.
- P. Raghavan, "Probabilistic Construction of Deterministic Algorithms: Approximating Packing Integer Programs", Journal of Computer and System Sciences 37(2), 1988.
