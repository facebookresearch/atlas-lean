---
article_id: af_5a7aa91ca0725338cfa2ed2b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.CarrollIdentity.carroll_identity
---

# Carroll Identity

Carroll (Dodgson condensation) identity: for an `(n + 2) × (n + 2)` matrix
over a commutative ring and arbitrary distinct indices `i j`, the product of the
full determinant with the double-deletion minor equals the difference of the
products of complementary single-deletion minors.

The `(n + 2) × (n + 2)` indexing permits two distinct deleted indices `i ≠ j`.
Each single-deletion minor (via `Fin.succAbove`) has size `n + 1`, while the
double minor deleting both `i` and `j` has size `n`. For `n = 0`, the double
minor is a `0 × 0` matrix, whose determinant in Mathlib is `1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.CarrollIdentity](../../../../../sources/v2/MathlibExt.md)
- Charles Delorme and Guillermo Pineda-Villavicencio, "Quadratic Form Representations via Generalized Continuants", Journal of Integer Sequences 18 (2015), Article 15.6.4, displayed lemma lines 133–142. Stable source URL: https://cs.uwaterloo.ca/journals/JIS/VOL18/Pineda/pin2.tex Verified source-file SHA-256: `ce4b0fb99a549cee767baa4defe39148a2cfa410e48b8919e20efcecb26a7169`. Verified normalized no-final-newline span SHA-256: `26bf5c11571feef0d9bbd84618b3819749cd8e8e2bd83239b235cdc627030542`. The source cites C. L. Dodgson, "Condensation of determinants, being a new and brief method for computing their arithmetical values", Proc. Roy. Soc. Lond. 15 (1866), 150–155. Proves `Wanted` entry `carroll_identity`.
