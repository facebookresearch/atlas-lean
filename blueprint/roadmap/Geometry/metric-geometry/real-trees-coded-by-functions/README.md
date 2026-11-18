# Real trees coded by functions

A continuous function $g$ codes a tree: $d_g(s, t) = g(s) + g(t) - 2 \min_{[s \wedge t, s \vee t]} g$ is a
pseudometric whose metric quotient is the real tree $T_g$ (Le Gall, *Random trees and
applications*, Section 2.2). It is the continuous version of the coding of a plane tree by its
contour path; coded by the normalised Brownian excursion, it gives Aldous's continuum random tree,
the starting point of the Brownian snake and of the Brownian map.

- [Minimum of a function between two times](tree-min.md)
- [Distance coded by a function](tree-dist.md)
- [The tree coded by a function](coded-tree.md)
- [Distance in the coded tree](dist-eq.md)
- [The minimum is a lower bound](tree-min-le.md)
- [The minimum is the greatest lower bound](le-tree-min.md)
- [The minimum lies below the left endpoint value](tree-min-le-left.md)
- [The minimum lies below the right endpoint value](tree-min-le-right.md)
- [Minimum over a single point](tree-min-self.md)
- [Monotonicity of the minimum](tree-min-anti.md)
- [Symmetry of the minimum](tree-min-comm.md)
- [Splitting the minimum](tree-min-of-le-of-le.md)
- [Ultrametric inequality for the minimum](min-tree-min-le.md)
- [Symmetry of the coded distance](tree-dist-comm.md)
- [The coded distance is nonnegative](tree-dist-nonneg.md)
- [The coded distance vanishes on the diagonal](tree-dist-self.md)
- [Triangle inequality for the coded distance](tree-dist-triangle.md)
- [Four-point inequality for the minimum](tree-min-four-point.md)
- [The tree coded by a continuous function is $0$-hyperbolic](is-delta-hyperbolic-zero.md)
- [Uniform continuity of the minimum in the coding function](abs-tree-min-sub-le.md)
- [The coding is $4$-Lipschitz for the uniform norm](abs-tree-dist-sub-le.md)

## Related topics

- [Gromov-hyperbolic spaces](../gromov-hyperbolic-spaces/README.md): a geodesic metric space is a
  real tree exactly when it is $0$-hyperbolic.
- [Pointed Gromov–Hausdorff convergence](../pointed-gromov-hausdorff-convergence/README.md): the
  topology in which coded trees converge when their coding functions converge uniformly.
- [Galton–Watson process](../../../Probability/branching-processes/galton-watson-process/README.md):
  the discrete trees whose rescaled contour functions converge to the Brownian excursion
  (Aldous's theorem).
- [Construction and sample paths of Brownian motion](../../../Probability/stochastic-calculus/construction-and-sample-paths-of-brownian-motion/README.md):
  Brownian excursions code the continuum random tree.
