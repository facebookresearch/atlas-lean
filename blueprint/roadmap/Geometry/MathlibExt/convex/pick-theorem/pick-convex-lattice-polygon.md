---
article_id: af_b749a003e750d50d3ed8dda5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pick_convex_lattice_polygon
---

# Pick convex lattice polygon

Pick's area formula for convex standard-lattice polygons:
`area = I + B / 2 - 1`, where `I` counts interior lattice points and `B`
counts boundary lattice points. The polygon is the full-dimensional convex
hull of finitely many integer-coordinate vertices (`hfull` rules out
degenerate cases); `B` counts integer points on the frontier of the hull.

Proof: The triangle case counts lattice points in a half-open fundamental
parallelogram. A crossing diagonal then cuts larger polygons into two smaller
full-dimensional lattice polygons, allowing strong induction on the vertex set.

## Depends on

This node has no prerequisites.

## Proof depends on

- [To Real volume convex Hull lattice triangle](to-real-volume-convex-hull-lattice-trian.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Convex.PickTheorem](../../../../../sources/v2/MathlibExt.md)
- Eugen J. Ionascu, "A Parametrization of Equilateral Triangles Having Integer Coordinates", Journal of Integer Sequences 10 (2007), Article 07.6.7, standard formula `Area = #b / 2 + #i - 1`, lines 87–100, <https://cs.uwaterloo.ca/journals/JIS/VOL10/Ionascu/ionascu2.tex>; Kevin A. Broughan, "The gcd-sum function", Journal of Integer Sequences 4 (2001), Article 01.2.2, trapezium application, lines 699–715 (the prose there prints "+1" but the paper's own derived formula, equation label `10`, uses the minus-one form), <https://cs.uwaterloo.ca/journals/JIS/VOL4/BROUGHAN/gcdsum.tex>; Gil Alon and Pete L. Clark, "On the Number of Representations of an Integer by a Linear Form", Journal of Integer Sequences 8 (2005), Article 05.5.2, generalized lattice version `A(P) = δ * (h + b / 2 - 1)`, lines 633–638 (this module is the `δ = 1` standard-lattice case), <https://cs.uwaterloo.ca/journals/JIS/VOL8/Clark/clark80.tex>.
