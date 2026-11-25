---
declaration: def
origin: cited
statement: formalized
lean: CDIS.genInv, CDIS.genInv_cdf_dirac_one
---

# Generalized inverse of a distribution function

CDIS id 93. For a distribution function `F` and `u ∈ ]0,1[`,
 `F⁻(u) = inf {x ∈ ℝ | F(x) ≥ u}`. In Lean the function is total: it returns the junk value
 `0` for `u ≤ 0` and `u > 1`, while at `u = 1` it is the genuine infimum of `{x | F(x) ≥ 1}`
 when that set is nonempty and bounded below (`5` for the Dirac mass at `5`). Every statement
 carries `u ∈ ]0,1[`.

## Depends on

No prerequisite in this chapter.

## Sources

- [Probabilités V, Méthode d'inversion, Réciproque généralisée](../../sources/cdis-probabilites-v.md)
