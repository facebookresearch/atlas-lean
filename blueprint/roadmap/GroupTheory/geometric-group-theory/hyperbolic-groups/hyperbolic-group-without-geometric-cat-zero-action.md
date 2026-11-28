# A word-hyperbolic group with no geometric CAT(0) action

There exist a finite simplicial complex $K$, a point $x$ in its barycentric realization, and $C\ge0$ such that $|K|$ is connected and all its homotopy groups in degrees $\ge2$ at $x$ are trivial. Every closed edge loop admitting a combinatorial disk has a disk using at most $C$ times its edge length noncollapsed triangles: insertion/removal of stutters and spurs has cost zero and each noncollapsed triangle move costs one.

The group $G=\pi_1(|K|,x)$ is word-hyperbolic for the four-point word-distance inequality of some finite generating set but has no proper cocompact isometric action on any nonempty proper complete geodesic CAT(0) space. No finite simplicial complex homotopy equivalent to $|K|$ admits a topology-compatible geodesic metric with each point having an open ball satisfying CAT($-1$) (the cosh midpoint comparison). No bound on the dimension of $K$ and no locally CAT(0) exclusion are asserted.

## Depends on

- [CAT(0) four-point comparison](../../../Geometry/metric-geometry/cat-0-spaces/is-cat0-four-point.md)
- [Word-hyperbolicity model](is-hyperbolic.md)
- Barycentric realization, disk move counts, word metric and compatible local CAT($-1$) metrics.

## Proof depends on

- Asphericity and the linear filling estimate for the same complex, and the separate obstruction to geometric CAT(0) actions.

## Expansion

Prove the convention bridges between counted disk moves and van Kampen disks, and between four-point and source CAT comparisons with geodesicity. Then derive the homotopy-type exclusion without weakening it to a statement about the chosen triangulation.

## Sources

- OpenAI Math, [`main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/HyperbolicObstruction.lean#L154-L155) (statement and local definitions).
