---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.FieldTheory.EssentialDimensionSymmetricWanted.edSn_five_wanted
---

# Ed Sn five wanted

Source: Buhler--Reichstein (1997), exact value `ed_ℂ(S₅) = 2`: their
general bounds `⌊5/2⌋ ≤ ed_ℂ(S₅) ≤ 5 - 3` coincide at `2`. The classical
Bring--Jerrard form `X^5 + pX + q` is not the descent behind that upper
bound here: producing it already requires solving auxiliary equations
over an extension of the coefficient field, and normalizing further to
`X^5 + X + a` is again only a scaling over an extension, so neither form
witnesses a descent over the original field in the sense of this file
(in particular nothing here implies `edSn 5 ≤ 1`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.AlgebraicGeometry.EssentialDimensionSymmetricWanted](../../../../sources/v2/WantedExt.md)
