# Nodal upper-bound counterexamples near the round three-sphere

Use the sign $-\Delta_g u=\lambda u$ for eigenvalues, with real nonzero smooth functions. In local coordinates $\Delta_g u=(\det g)^{-1/2}\partial_i((\det g)^{1/2}g^{ij}\partial_j u)$, summing repeated indices. Measure the zero set with respect to the intrinsic metric of $g$. For a fixed metric $g$ in dimension $d$, require a sequence $u_j$ of such eigenfunctions with $\lambda_j>0$, $\lambda_j\to\infty$, each nodal $(d-1)$-dimensional Hausdorff measure finite, and $\mathcal H_g^{d-1}(\{u_j=0\})/\sqrt{\lambda_j}\to+\infty$.

For each metric $g_0$ on the unit $S^3$ equal to the round metric induced by Euclidean inclusion, every smooth neighborhood of $g_0$ contains a single smooth metric $g$ with this property for $d=3$. A smooth neighborhood here contains a basic neighborhood tested by finitely many sup bounds, with one positive tolerance, on derivatives of differences in metric coefficients over compact subsets of chart targets.

## Depends on

- [Laplace–Beltrami operator](../laplacian.md)
- Smooth metric topology from compact-chart jet tests and intrinsic Hausdorff nodal measure.

## Proof depends on

- Construct one perturbed metric within the prescribed tests and produce the complete sequence for that same metric.

## Expansion

Compare the finite compact-chart seminorm condition with the in-repo metric regularity topology. Separate metric construction and the estimates on intrinsic nodal sets.

## Sources

- OpenAI Math, [`sphere_three`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SmoothYau.lean#L132-L138) (statement and local definitions).
