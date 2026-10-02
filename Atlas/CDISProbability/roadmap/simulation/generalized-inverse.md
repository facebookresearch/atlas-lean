---
declaration: def
origin: cited
statement: formalized
lean: CDIS.genInv
---

# Generalized inverse of a distribution function

CDIS id 93. For a distribution function `F` and `u ∈ ]0,1[`,
 `F⁻(u) = inf {x ∈ ℝ | F(x) ≥ u}`. In Lean the function is total; outside `]0,1[` the
 infimum returns the junk value `0`, and every statement carries `u ∈ ]0,1[`.

## Depends on

No prerequisite in this chapter.

## Sources

- [Probabilités V, Méthode d'inversion, Réciproque généralisée](../../sources/cdis-probabilites-v.md)
