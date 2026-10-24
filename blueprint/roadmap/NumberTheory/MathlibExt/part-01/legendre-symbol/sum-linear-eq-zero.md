---
article_id: af_e759fb21be42c5fea0f72928
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: legendreSym.sum_linear_eq_zero
---

# Linear Sum

A linear Legendre-symbol sum over a complete residue system vanishes when
the slope is nonzero modulo the odd prime `p`.

This is the first corollary of Theorem `thm1` in Ram Krishna Pandey and
Anshumaan Parashar, *On Certain Sums with Quadratic Expressions Involving the
Legendre Symbol*, Journal of Integer Sequences 21 (2018), Article 18.4.7,
lines 190–193,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Pandey/pandey14.tex>.
The proof here reindexes Mathlib's `quadraticChar_sum_zero`
through the affine permutation `x ↦ b * x + c` of `ZMod p`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.LegendreSymbol.LinearSum](../../../../../sources/v2/MathlibExt.md)
