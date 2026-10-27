---
article_id: af_2c5acbd2dcf325d06e78cf83
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.galDetHom
---

# Gal Det Hom

The determinant of the mod-`p` representation, as a character with values
in `(ZMod p)ˣ`. `LinearEquiv.det` is basis independent (Mathlib proves
`detAux` does not depend on the basis), so no basis of `E[p]` is fixed.
It is defined unconditionally: on a module with no finite basis it takes the
value `1`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gal Rep](gal-rep.md)
- [Torsion Pts](torsion-pts.md)

## Sources

- [MathlibExt, MathlibExt.AlgebraicGeometry.EllipticCurve.GaloisRepresentation](../../../../../sources/v2/MathlibExt.md)
