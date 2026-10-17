---
article_id: af_896343bec23515c3a10e5d2c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bell_eq_signed_stirlingFirst_convolution
---

# Bell Convolution

New double-sum formula for Bell numbers via Spivey's formula and Stirling
numbers of the first kind.

Mathlib's `Nat.stirlingFirst` is the unsigned Stirling number of the first
kind, so `(-1)^(p-m) * stirlingFirst p m` is the signed `s(p,m)` of the
source. The source states `p ≥ 1` and notes the `0^0 = 1` convention extends
the formula to `p = 0`, matching Lean.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BellConvolution](../../../../../../sources/v2/MathlibExt.md)
- H. W. Gould and Jocelyn Quaintance, "Implications of Spivey's Bell Number Formula," Journal of Integer Sequences 11 (2008), Article 08.3.7, Theorem, equation (E:4), lines 177–182, https://cs.uwaterloo.ca/journals/JIS/VOL11/Gould/gould35.tex
