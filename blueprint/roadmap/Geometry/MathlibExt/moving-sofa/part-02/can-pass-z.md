---
declaration: def
origin: cited
statement: formalized
lean: MovingSofa.CanPassZ
---

# Can Pass Z

The shape passes the Z corridor for all sufficiently large corner
separations (equivalently, `∀ᶠ d in Filter.atTop, CanPassZAt K d`):
the source's "sufficiently separated corners". Unlike the mirrored
corridor, this is not implied by an ordinary passage: time reversal
plus a rigid motion transports an ordinary passage to the *mirrored*
corridor, but a Z passage couples both turns in one motion.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Can Pass ZAt](can-pass-zat.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.MovingSofa](../../../../../sources/v2/MathlibExt.md)
