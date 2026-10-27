---
article_id: af_6435cda993766cfe7d076563
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.galLinearEquiv
---

# Gal Linear Equiv

The invertible `ZMod p`-linear action of a Galois automorphism on `E[p]`,
packaged via `LinearEquiv.ofBijective` to avoid normalizing
`toZModLinearMap` projections inside a manual `LinearEquiv` construction.

## Depends on

- [Torsion Pts](torsion-pts.md)

## Proof depends on

- [Gal Linear Map](gal-linear-map.md)
- [Gal Linear Map bijective](gal-linear-map-bijective.md)

## Sources

- [MathlibExt, MathlibExt.AlgebraicGeometry.EllipticCurve.GaloisRepresentation](../../../../../sources/v2/MathlibExt.md)
