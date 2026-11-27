# A fixed nodal upper-bound counterexample on S² × T²

Use the sign $-\Delta_g u=\lambda u$ for eigenvalues, with real nonzero smooth functions. In local coordinates $\Delta_g u=(\det g)^{-1/2}\partial_i((\det g)^{1/2}g^{ij}\partial_j u)$, summing repeated indices. Measure the zero set with respect to the intrinsic metric of $g$. For a fixed metric $g$ in dimension $d$, require a sequence $u_j$ of such eigenfunctions with $\lambda_j>0$, $\lambda_j\to\infty$, each nodal $(d-1)$-dimensional Hausdorff measure finite, and $\mathcal H_g^{d-1}(\{u_j=0\})/\sqrt{\lambda_j}\to+\infty$.

There is a smooth metric on the product of the unit two-sphere with two copies of the circle with this property for $d=4$. The statement requires no closeness to the product round metric.

## Depends on

- [Laplace–Beltrami operator](../laplacian.md)
- Smooth product manifold, intrinsic Hausdorff nodal measure for the chosen metric.

## Proof depends on

- Metric construction and growth of the finite intrinsic nodal measures along a single eigensequence.

## Expansion

Keep the metric fixed outside the sequence quantifier and verify the lower estimates with the intrinsic distance of this metric, not the ambient round distance.

## Sources

- OpenAI Math, [`sphere_two_torus_two`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SmoothYau.lean#L139-L145) (statement and local definitions).
