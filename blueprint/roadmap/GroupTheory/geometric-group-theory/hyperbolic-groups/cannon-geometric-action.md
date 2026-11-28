# Cannon’s spherical-boundary geometric action conclusion

Let $G$ be a discrete group with a finite inverse-closed generating set and connected Cayley graph. Assume that some natural $\delta$ uniformly bounds the distance of every vertex of each shortest-path triangle side to the other two sides. Form the boundary as the quotient of integer-time distance-preserving rays based at the identity by uniformly bounded synchronous distance, with quotient topology from the product of discrete vertex spaces. Suppose this boundary is homeomorphic to the unit two-sphere.

Then there is a homomorphism $\rho:G\to\operatorname{Isom}(\mathbb H^3)$, allowing orientation reversal, with finite kernel and proper cocompact action. In upper half-space the preserved distance is $\operatorname{arcosh}(1+\|x-y\|_2^2/(2x_3y_3))$. Proper means that for any compact $K$ only finitely many $g$ have $gK\cap K\ne\varnothing$; cocompact means translates of a single compact set cover $\mathbb H^3$.

## Depends on

- [Existing group hyperbolicity model](is-hyperbolic.md)
- Ray quotient boundary with its topology; upper-half-space distance and full isometry group.

## Proof depends on

- Boundary modulus and realization of the action in the upper-half-space model.

## Expansion

Compare the ray boundary and thin triangles with the usual hyperbolicity infrastructure. Keep the conclusion as a geometric action with finite kernel rather than claiming an embedding or orientation-preserving action.

## Sources

- OpenAI Math, [`cannon`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CannonGeometricAction.lean#L89-L95) (statement and local definitions).
