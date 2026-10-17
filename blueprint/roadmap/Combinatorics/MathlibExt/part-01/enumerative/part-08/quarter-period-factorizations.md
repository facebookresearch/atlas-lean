---
article_id: af_b6ceabb1f0af58b2a20fb9e2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.quarter_period_factorizations
---

# Triangular Strip Tilings

Quarter-period factorizations for the number `Q n` of tilings of a triangular
strip: with `Q 0 = Q 1 = 1`, `Q 2 = 4`, and
`Q n = Q (n - 1) + 3 * Q (n - 2) + Q (n - 3)` for `n ≥ 3`, the values at
`4 * m`, `4 * m + 1`, `4 * m + 2`, `4 * m + 3` factor through the values at
`2 * m - 1`, `2 * m`, `2 * m + 1`.

The recurrence and initial values are equation (rec) at lines 122–125.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.TriangularStripTilings](../../../../../../sources/v2/MathlibExt.md)
- Mark Shattuck, "Combinatorial Proofs of Some Formulas for Triangular Tilings," Journal of Integer Sequences 17 (2014), Article 14.5.5, Theorem (label thm2, due to Bodeen et al.), lines 103–112, https://cs.uwaterloo.ca/journals/JIS/VOL17/Shattuck/shattuck8.tex
