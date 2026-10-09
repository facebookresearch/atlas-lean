---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.map_genInv_cdf, CDIS.hasLaw_genInv_cdf, CDIS.hasLaw_genInv_cdf_map
---

# Inversion method

CDIS id 94. If `U` is uniform on `]0,1[`, then `F⁻(U)` has distribution function `F`.
 Proof: `{F⁻(U) ≤ x} = {U ≤ F(x)}` on `]0,1[` by the Galois connection, so both laws have
 the same distribution function.

## Depends on

- [Generalized inverse](generalized-inverse.md)

## Proof depends on

- [Properties of the generalized inverse](generalized-inverse-properties.md)

## Sources

- [Probabilités V, Méthode d'inversion](../../sources/cdis-probabilites-v.md)
