---
article_id: af_716c15d193670319842085b8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.euler_quadrilateral
---

# Euler Quadrilateral

Euler's quadrilateral theorem (statement `euler-quadrilateral-s1` from
https://en.wikipedia.org/wiki/Euler%27s_quadrilateral_theorem): a quadrilateral
with sides `a`, `b`, `c`, `d`, diagonals `e`, `f`, and segment `m` joining the
diagonal midpoints satisfies `a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = e ^ 2 + f ^ 2 + 4 * m ^ 2`.
Lengths are Euclidean `dist` and midpoints are averages.
Proves `Wanted` entry `MetaMathlibExt.euler_quadrilateral`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.EulerQuadrilateral](../../../../../sources/v2/MathlibExt.md)
