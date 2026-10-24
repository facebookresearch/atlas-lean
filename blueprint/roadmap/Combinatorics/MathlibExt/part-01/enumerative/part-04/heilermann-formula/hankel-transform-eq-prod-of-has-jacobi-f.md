---
article_id: af_6628debf4d5bd04db96cdf11
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hankelTransform_eq_prod_of_hasJacobiFraction
---

# Hankel Transform eq prod of has Jacobi Fraction

Heilermann's formula: the Hankel transform of a sequence with Jacobi
continued fraction data `(alpha, beta, mu0)` is
`h_n = mu0 ^ (n + 1) * beta_1 ^ n * beta_2 ^ (n - 1) * ... * beta_n ^ 1`.

## Depends on

- [Has Jacobi Fraction](../../../../../../NumberTheory/MathlibExt/part-06/hankel-transform/has-jacobi-fraction.md)
- [Hankel Transform](../../../../../../NumberTheory/MathlibExt/part-06/hankel-transform/hankel-transform.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.HeilermannFormula](../../../../../../../sources/v2/MathlibExt.md)
- Paul Barry, "From Fibonacci to Robbins: Series Reversion and Hankel Transforms," Journal of Integer Sequences 24 (2021), Article 21.10.2, `https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex`, lines 110-117. Normalized source-text SHA-256 (no terminal newline) `a838e5996f223ba9e45347f17ad864912efc392f5c3d56ea749bcf62d3289825`; raw line-span SHA-256 (with terminal newline) `11385eb5eee1af1081307348d4029cdc74b51d84e8bff2fbe9831891145d998e`. Concept `jis_dep_heilermann_049f63eb`; grounded `jis_grounded_049f63eb8aadf7377777a597`. Zero-indexed: `hankelTransform a n` is the determinant of the `(n + 1) x (n + 1)` Hankel matrix, and the product over `Finset.range n` with shift `beta (j + 1)` and exponent `n - j` gives `beta_1 ^ n, ..., beta_n ^ 1`; for `n = 0` the empty product yields `mu0`. Scope: only the determinant identity is stated; the Jacobi continued fraction data itself is carried by `HasJacobiFraction`.
