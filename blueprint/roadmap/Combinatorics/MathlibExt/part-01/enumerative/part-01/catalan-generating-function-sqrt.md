---
article_id: af_624da7118c93d35c691cb3bb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.CatalanGeneratingFunction.catalan_generating_function_sqrt
---

# Catalan Generating Function

Convergent real specialization of the Catalan generating function for `|x| < 1 / 4`:
`∑' n, catalan n * x ^ n = (1 - √(1 - 4 * x)) / (2 * x)`.

The hypothesis `x ≠ 0` excludes the displayed formula's removable singularity at `x = 0`.
Mathlib has `PowerSeries.catalanSeries` and its quadratic functional equation, but its
source file explicitly lists the square-root closed form as a TODO; this theorem records
the analytic closed form rather than duplicating the formal series definition.

Provenance: Paul Barry, "A Note on a Family of Generalized Pascal Matrices Defined by
Riordan Arrays", Journal of Integer Sequences 16 (2013), Article 13.5.4, proposition
lines 380–388, <https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry2/barry231.tex>.
Complete-source SHA-256 `2d55112a4e158236133ce50b992c0a6eb75ceb48446695581e4dbe8e35879161`;
normalized proposition-span SHA-256
`d350c0634eccfd92e38924751b09c94be26086fca3c50da195c8a353910dc759`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.CatalanGeneratingFunction](../../../../../../sources/v2/MathlibExt.md)
