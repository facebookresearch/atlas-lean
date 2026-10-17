---
article_id: af_06d274b759290ad4f0f7eb56
declaration: def
origin: cited
statement: formalized
lean: BinaryQuadraticForm.IsGaussReduced
---

# Reduced

Gauss reducedness for the integral binary quadratic form
`a*x^2 + b*x*y + c*y^2` in the strict source convention:

`IsGaussReduced a b c` holds iff `0 < a`, `discrim a b c < 0`,
`|b| ≤ a`, `a ≤ c`, and `(|b| = a ∨ a = c) → 0 ≤ b`.

This is Mortenson `arXiv:1702.01627v2` Section 2 line 259. In particular
`(1,-1,1)` is positive definite and satisfies the loose inequalities but
is not reduced because the tie-break requires `b ≥ 0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.QuadraticForms.Reduced](../../../../../sources/v2/MathlibExt.md)
