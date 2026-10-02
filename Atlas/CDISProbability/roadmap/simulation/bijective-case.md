---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.IsCdfBijection.hasLaw_comp, CDIS.IsCdfBijection.hasLaw_cdf_comp
---

# Inversion when the distribution function is bijective

CDIS id 92. If `F` maps some `]a,b[` bijectively onto `]0,1[` with inverse `G`, then
 `G(U)` has the law of `X` and `F(X)` is uniform on `]0,1[`. `G` coincides with `F⁻` on
 `]0,1[`, so the first claim reduces to the inversion method.

## Depends on

No prerequisite in this chapter.

## Proof depends on

- [Inversion method](inversion-method.md)

## Sources

- [Probabilités V, Cas où F_X est bijective](../../sources/cdis-probabilites-v.md)
