---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: CDIS.genInv_le_iff, CDIS.le_genInv_of_apply_lt, CDIS.monotoneOn_genInv, CDIS.genInv_apply_le, CDIS.le_apply_genInv', CDIS.apply_genInv_of_mem_range
---

# Properties of the generalized inverse

CDIS id 101. `F⁻` is nondecreasing on `]0,1[`; `F⁻(F(x)) ≤ x` when `F(x) > 0`
 (the course omits this hypothesis, without which `F⁻(F(x))` is outside the domain);
 `F(F⁻(u)) ≥ u` with equality on the range of `F`; and the Galois connection
 `F(x) ≥ u ↔ x ≥ F⁻(u)`. Right continuity of `F` is what puts `F⁻(u)` in `{x | F(x) ≥ u}`.

## Depends on

- [Generalized inverse](generalized-inverse.md)

## Sources

- [Probabilités V, Annexe, Preuve de la méthode d'inversion](../../sources/cdis-probabilites-v.md)
