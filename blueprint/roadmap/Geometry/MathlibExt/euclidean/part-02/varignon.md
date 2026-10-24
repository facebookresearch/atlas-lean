---
article_id: af_21bdf068ce7ead1ce504e2a8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.varignon
---

# Varignon

Varignon's theorem (statement varignon-s1): side-midpoints of any quadrilateral form
a parallelogram of half the area.

## Depends on

- [Oriented Triangle Area](../../two-d/oriented-triangle-area.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Varignon](../../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Varignon%27s_theorem. `A B C D` are arbitrary points in the Euclidean plane, including degenerate or self-crossing configurations. `P Q R S` are the midpoints of sides AB, BC, CD, DA (`2 • P = A + B`, etc.). Conclusion: `P + R = Q + S` (the diagonals of PQRS bisect each other, i.e. PQRS is a parallelogram via parallel opposite sides / bisecting diagonals), and twice the signed area of PQRS, expressed through `EuclideanGeometry.orientedTriangleArea`, equals the signed area of ABCD.
