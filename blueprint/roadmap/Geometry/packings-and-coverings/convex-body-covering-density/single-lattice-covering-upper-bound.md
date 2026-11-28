# A single-lattice covering bound of order n log n

There is an absolute real constant $C>0$ such that, for every integer $n\ge2$ and every convex body $K\subset\mathbb R^n$, some discrete full-rank additive lattice $L\le\mathbb R^n$ satisfies

$$K+L=\mathbb R^n,\qquad |K|/\operatorname{covol}(L)\le Cn\log n.$$

Every point must be covered, not merely almost every point. The numerator and covolume are the ordinary Lebesgue quantities in real coordinates, without symmetry or volume normalization.

## Depends on

- [Convex body](../hadwiger-covering-and-illumination-problem/is-convex-body.md)
- Coordinate lattice covolume and its comparison with Euclidean Haar volume.

## Proof depends on

- One-lattice construction with uniform dimension-dependent density bound (not a union of covering translates of several lattices).

## Expansion

Reuse Mathlib’s discrete full-rank lattice and covolume, align the coordinate and Euclidean volume conventions, and break out the construction and exact covering argument for arbitrary convex bodies.

## Sources

- OpenAI Math, [`single_lattice_covering`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SingleLatticeCovering.lean#L20-L26) (statement and local definitions).
