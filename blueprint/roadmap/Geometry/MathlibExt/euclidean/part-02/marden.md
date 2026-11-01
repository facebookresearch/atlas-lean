---
article_id: af_7b8feba819584c198df940ab
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.marden
---

# Marden

Marden's theorem (statement `marden-s1`): the foci of the Steiner inellipse,
  tangent at the edge midpoints of a nondegenerate triangle with vertices `a`, `b`, `c`,
  are the zeros of the derivative of `(z - a) * (z - b) * (z - c)`, allowing coincident
  foci for the equilateral (circular) case. The inellipse is encoded by the common
  distance sum `L` through the three edge midpoints plus tangency of each sideline
  at its midpoint.

Proof: The statement is Marden's theorem (M. Marden, *Geometry of Polynomials*, 2nd ed.,
Math. Surveys No. 3, AMS, 1966; D. Kalman, *An Elementary Proof of Marden's Theorem*,
Amer. Math. Monthly 115(4) (2008), 330-338, <https://doi.org/10.1080/00029890.2008.11920532>).
Following [Wikipedia, *Marden's theorem*](https://en.wikipedia.org/wiki/Marden%27s_theorem),
we use Vieta's relations, the midpoint identity for the derivative, and the ellipse reflection
property expressed by a strict triangle inequality.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Marden](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Marden%27s_theorem.
