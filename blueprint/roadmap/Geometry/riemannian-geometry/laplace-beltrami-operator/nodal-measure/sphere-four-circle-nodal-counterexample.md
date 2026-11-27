# A fixed nodal upper-bound counterexample on S⁴ × S¹

Use the sign $-\Delta_g u=\lambda u$ for eigenvalues, with real nonzero smooth functions. In local coordinates $\Delta_g u=(\det g)^{-1/2}\partial_i((\det g)^{1/2}g^{ij}\partial_j u)$, summing repeated indices. Measure the zero set with respect to the intrinsic metric of $g$.

There is a smooth metric $g$ on the product of the unit four-sphere with a circle, and positive real eigenvalues $\lambda_j\to+\infty$ with real nonzero smooth eigenfunctions $u_j$ for $g$, for which the ratios $\mathcal H_g^4(\{u_j=0\})/\sqrt{\lambda_j}$ tend to top **in the extended nonnegative reals**. The selected endpoint does not separately require the nodal measure of each eigenfunction to be finite.

## Depends on

- [Laplace–Beltrami operator](../laplacian.md)
- Product manifold charts and intrinsic four-dimensional Hausdorff measure.

## Proof depends on

- Metric, eigenfunction realization and nodal lower bounds with the same metric through the whole sequence.

## Expansion

Bridge the coordinate and intrinsic Laplacian and establish the limit in the extended range rather than silently converting infinite measures to zero.

## Sources

- OpenAI Math, [`yau_nodal_set_upper_bound_counterexample`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/YauCounterexample.lean#L65-L67) (statement and local definitions).
