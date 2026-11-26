# Sharp filling of compactly supported integral cycles in proper CAT(0) spaces

Write $\omega_{n+1}$ for the Euclidean volume of the open unit ball in $\mathbb R^{n+1}$ and put $a_n=(n+1)\omega_{n+1}$ and $c_n=1/((n+1)a_n^{1/n})$. The source uses integral metric currents in the finite-mass sense, with integer rectifiability for both $T$ and $\partial T$: disjoint images of bounded Borel bi-Lipschitz coordinate pieces, integrable integer multiplicities, and summable masses. Mass is the infimum of the total masses of finite measures bounding the current on a bounded Lipschitz coefficient and unit-Lipschitz coordinate functions.

Let $X$ be a proper metric space with its Borel measurable structure. Require chosen constant-speed segments between any two points, with squared-distance Euclidean comparison for pairs of points on segments issuing from a common origin. For every integer $n\ge2$ and every compactly supported integral $n$-current $T$ with $\partial T=0$, there is a compactly supported integral $(n+1)$-current $S$ with $\partial S=T$ and $\mathbf M(S)\le c_n\mathbf M(T)^{(n+1)/n}$. In particular the zero cycle is allowed.

## Depends on

- [CAT(0) four-point comparison](../../../Geometry/metric-geometry/cat-0-spaces/is-cat0-four-point.md)
- Integral metric currents in arbitrary proper spaces, mass, support and boundary; comparison of the segment model with the four-point CAT(0) condition plus geodesicity.

## Proof depends on

- Mass control, integrality and compactness in the CAT(0) filling construction with the exact Euclidean coefficient.

## Expansion

Introduce the common current model and chart comparison first, then factor the sharp filling estimate into the construction, integrality, and preservation of compact support. The Euclidean optimality endpoint is separate.

## Sources

- OpenAI Math, [`sharp_integral_filling`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SharpCAT0Filling.lean#L135-L143) (statement and local definitions).
