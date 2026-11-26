# At most two limit cycles in the quintic Liénard model

For every real polynomial $F$ of degree at most five, the system $\dot x=y-F(x),\ \dot y=-x$ has at most two limit cycles. A periodic orbit is the image of a nonconstant solution $z:\mathbb R\to\mathbb R^2$ solving the differential equation at all times, with some period $T>0$. Its image $C$ is a limit cycle if some open set containing $C$ contains no other complete periodic-orbit image. Count distinct images, not times, parameterizations or periods. There are no restrictions on signs, parity or hyperbolicity, and the zero polynomial is included.

## Depends on
The autonomous planar polynomial vector field, the global solution convention and isolation of a periodic image in an open containing set.

## Proof depends on
A return-map or equivalent planar analysis bounding all distinct isolated cycles, including degenerate polynomial coefficients and nonhyperbolic cycles.

## Expansion
Derive the relevant return-map expression and establish a root-counting/sign-change bound that respects orbit images and possible degenerate cases. This does not assert uniform boundedness for all planar polynomial vector fields.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/QuinticLienard.lean#L39-L43) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/143.md).
