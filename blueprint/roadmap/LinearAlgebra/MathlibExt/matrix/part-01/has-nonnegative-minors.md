---
article_id: af_3e22249e87fb5f5383dddd9a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.Matrix.HasNonnegativeMinors
---

# Nonnegative Minors

A rectangular real matrix has nonnegative minors when every finite square
submatrix selected by strictly increasing row and column maps has nonnegative
determinant. The quantification over all `k : ℕ` includes the `0 × 0` minor
(`k = 0`).

This rectangular-indexed predicate is named for its defining property rather
than as a second spelling of Mathlib's square-matrix total-nonnegativity API.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.NonnegativeMinors](../../../../../sources/v2/MathlibExt.md)
- Ming-Jian Ding and Jiang Zeng, "Some New Results on the Minuscule Polynomials of Type A", Journal of Integer Sequences 28 (2025), Article 25.1.2, "Total positivity of the coefficient matrix" section (label `sec+TP`), definition at lines 638–639 (used by the Schoenberg–Edrei lemma, label `lem+SE+PF`, line 654), <https://cs.uwaterloo.ca/journals/JIS/VOL28/Zeng/zeng26.tex>.
