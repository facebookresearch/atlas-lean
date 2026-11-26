# Circle-domain rigidity from a removable source boundary

Let $U,V$ be connected open subsets of the Riemann sphere whose complementary connected components are points or Möbius images of the closed unit disk. Suppose $\partial U$ is conformally removable: it is compact, and every homeomorphism of the sphere homotopic to the identity that is conformal outside $\partial U$ is a Möbius transformation. A conformal equivalence $f:U\to V$ then agrees on $U$ with one Möbius transformation. Conformality is continuity and nonzero complex derivative in the local complex coordinate, using the reciprocal coordinate at infinity, for $f$ and its inverse. Removability is required for the source boundary only; the claim is not the converse direction.

## Depends on

Use the point-or-closed-disk definition of a circle domain, the spherical Möbius action, and the specified homotopy-based orientation convention.

## Proof depends on

A conformal equivalence must be extended to a homeomorphism to which source-boundary removability genuinely applies; arbitrary extensions over the complementary disks need not be conformal there.

## Expansion

Separate control of the boundary correspondence from the conformal extension over the interiors of the disk components. Verify global continuity, orientation, and conformality off the source boundary before applying removability.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KoebeCircleDomains.lean#L68-L74) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/071.md).
