---
article_id: af_d843a7b6862d10a45f966b7d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.meshPatternGeneratingFunction_eq_factorial_mul_prod_general
---

# Mesh Pattern Generating Function eq factorial mul prod general

Product formula for a sequence `P m k` in a commutative semiring satisfying the mesh-pattern
recurrence `P m k = (x + (m - 1)) * P (m - 1) k` for `k ≤ m`, with base value
`P (k - 1) k = (k - 1)!`. With `R := Polynomial ℕ` and `x := Polynomial.X` this is the product
formula for the mesh-pattern counting polynomial.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.MeshPatternGeneratingFunction](../../../../../../../sources/v2/MathlibExt.md)
- Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling Numbers," Journal of Integer Sequences 18 (2015), Article 15.10.1, Corollary (label cor:genfunc), line 194, with the recurrence and base value from Theorem (label thm:main), line 175, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.
