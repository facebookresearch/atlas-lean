---
article_id: af_e76da503cd1298f9fad479e6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Euclidean.JungWanted.jung
---

# Jung

Every bounded subset of finite-dimensional real Euclidean space is contained in a closed ball whose
radius is bounded by the sharp Jung constant times its diameter: `0 < n`, `Bornology.IsBounded s`,
existence of centre `c` with `s ⊆ closedBall c (√(n / (2(n+1))) * diam s)`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Convex Hull of compact](../../../../Analysis/MathlibExt/part-01/convex/straszewicz/part-01/convex-hull-of-compact.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Jung](../../../../../sources/v2/MathlibExt.md)
- H. Jung, Über die kleinste Kugel, die eine räumliche Figur einschließt, J. Reine Angew. Math. 123 (1901) 241–257 original theorem; D. Gale sharp Euclidean formulation; standard modern reference M. Berger, Geometry I & II. Proves `Wanted` entry `jung`.
