---
article_id: af_d2082e0a4b054a766e4b0bff
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.HasJacobiFraction
---

# Has Jacobi Fraction

Algebraic tail-witness predicate for a Jacobi continued fraction: the head
equation pins the numerator `mu0`, and each tail factor has linear term
`alpha i` and shifted quadratic numerator `beta (i + 1) x^2`, with minus signs.
This is only the algebraic boundary, not Heilermann's determinant identity.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.HankelTransform](../../../../../sources/v2/MathlibExt.md)
- Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel Transforms," JIS 24 (2021), Article 21.10.2, `https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex`, lines 110-117 (source SHA-256 `9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`; lines 110-117 SHA-256 `11385eb5eee1af1081307348d4029cdc74b51d84e8bff2fbe9831891145d998e`). JIS concept: `jis_dep_heilermann_049f63eb`.
