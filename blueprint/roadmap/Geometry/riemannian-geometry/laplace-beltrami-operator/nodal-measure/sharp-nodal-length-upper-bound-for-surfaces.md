# Nodal-length upper bound on a fixed smooth closed surface

Use the sign $-\Delta_g u=\lambda u$ for eigenvalues, with real nonzero smooth functions. In local coordinates $\Delta_g u=(\det g)^{-1/2}\partial_i((\det g)^{1/2}g^{ij}\partial_j u)$, summing repeated indices. Measure the zero set with respect to the intrinsic metric of $g$.

Let $M$ be a compact connected smooth Riemannian surface with distance agreeing with the Riemannian path distance. There is $C\ge0$ depending on the surface and metric such that for every $\lambda>0$ and every such eigenfunction at $\lambda$, its zero set has one-dimensional Hausdorff measure at most $C\sqrt\lambda$. Its lower bound is not part of the statement.

## Depends on

- [Laplace–Beltrami operator](../laplacian.md)
- Compare the coordinate divergence Laplacian with the intrinsic Laplace–Beltrami operator and its sign.

## Proof depends on

- Nodal-length upper estimate with a constant uniform over the entire positive eigenspectrum of the fixed metric.

## Expansion

Prove agreement of the chart coefficients with the native metric and verify the derivative on the chart target; verify that the measure is intrinsic, not ambient.

## Sources

- OpenAI Math, [`Main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NodalLength.lean#L52-L57) (statement and local definitions).
