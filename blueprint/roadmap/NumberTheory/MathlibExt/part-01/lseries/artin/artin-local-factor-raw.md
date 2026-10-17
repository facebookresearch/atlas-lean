---
article_id: af_7a57e106650f061f16cf07cc
declaration: def
origin: cited
statement: formalized
lean: Representation.artinLocalFactorRaw
---

# Artin Local Factor Raw

The totalized inverse of the Artin local denominator at the rational prime `p`.

`ρ` is restricted to the decomposition subgroup and the resulting
`I_w`-invariants carry the quotient action `G_w/I_w`; evaluating that
action at `frobenius` gives the operator whose determinant is inverted.
The hypothesis `[Module.Free ℂ V] [Module.Finite ℂ V]` makes the determinant
available via `LinearMap.det` on the finite-dimensional invariant subspace.
At a zero of the denominator, complex inversion gives the totalized value `0`;
use `ArtinLocalFactorRegular` when a genuine finite Euler factor is required.

## Depends on

- [Artin Local Datum](artin-local-datum.md)

## Proof depends on

- [Artin Local Denominator](artin-local-denominator.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.LSeries.Artin](../../../../../../sources/v2/MathlibExt.md)
