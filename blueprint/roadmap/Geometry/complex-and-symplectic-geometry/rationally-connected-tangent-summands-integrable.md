# Integrability of tangent summands on a rationally connected projective manifold

Let $X$ be a compact connected Hausdorff second-countable complex manifold of dimension at least two with a holomorphic injective projective immersion $e:X\to\mathbb P^N$. Require that on a nonempty dense Zariski-open subset of $X\times X$ each pair is joined by a holomorphic map $\mathbb P^1\to X$. Here the open subset is a union of nonvanishing loci of bihomogeneous polynomials in the homogeneous coordinates of the two images under $e$, and a rational curve has holomorphic maps in the two affine parameters agreeing by inversion on their overlap. For every holomorphic idempotent on $TX$ with positive fibre ranks for both range and kernel, both distributions are involutive: the Lie bracket of any two local holomorphic sections in the same summand belongs to that summand at every point of their open domain. No splitting of a universal cover is asserted here.

## Depends on

- [Complex atlas](../../AlgebraicGeometry/not-yet-classified/hyperkahler-complex-structures/complex-atlas.md)
- Projective immersion with holomorphic affine coordinate ratios, projective rational curves, holomorphic tangent projections and brackets.

## Proof depends on

- Integrability of each distribution from restrictions to rational curves through pairs in the specified open set.

## Expansion

Prove agreement of the two-chart rational-curve predicate with the projective manifold model, then isolate both bracket-closure obligations; do not build the conclusion into the notion of a tangent splitting.

## Sources

- OpenAI Math, [`integrability_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SplitTangentIntegrability.lean#L135-L137) (statement and local definitions).
