---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.isUniform_cond_preimage
---

# Stability of the uniform law under conditioning

CDIS id 96. If `U` is uniform on `A` and `B ⊆ A`, the law of `U` given `U ∈ B` is
 uniform on `B`. Follows from `(P[|U ∈ B]).map U = (P.map U)[|B]` and
 `cond_cond_eq_cond_inter`.

## Depends on

- [Uniform law](uniform-law.md)

## Sources

- [Probabilités V, Stabilité par conditionnement](../../sources/cdis-probabilites-v.md)
