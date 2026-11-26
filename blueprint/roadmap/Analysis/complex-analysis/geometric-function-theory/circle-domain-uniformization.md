# Circle-domain uniformization

Every connected open subset $U$ of the Riemann sphere $\mathbb C\cup\{\infty\}$ admits a conformal bijection onto a connected open subset $V$ of that sphere whose complementary connected components are each a single point or a Möbius image of the closed unit disk. A conformal equivalence and its inverse are continuous on their domains and have nonzero complex derivative in local coordinates: use the complex coordinate at finite points and reciprocal coordinate, taking $\infty$ to zero, at infinity. There is no cardinality restriction on the components of $U^c$ or $V^c$.

## Depends on

The spherical conformal atlas, the Möbius action of invertible complex two-by-two matrices on the sphere, and complementary connected components of arbitrary spherical open sets.

## Proof depends on

The uniformization construction must preserve roundness (or degeneration to a point) for each complementary component, not only for a countable subcollection.

## Expansion

Separate the approximating uniformizations and normalization from the limit argument. Prove a nondegenerate conformal limit and identify all complementary components, including singleton limits. A planar simply connected Riemann mapping result alone does not supply this step.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KoebeCircleDomains.lean#L62-L67) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/071.md).
