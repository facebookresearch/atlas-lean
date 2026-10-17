---
article_id: af_a87a5320cdf90097b62a7443
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.hankelTransform_eq_prod_of_weightedMotzkin
---

# Heilermann Weighted Motzkin Determinant

Weighted-Motzkin determinant form of Heilermann's formula: the Hankel
transform of the zeroth column of a weighted-Motzkin triangle is
`mu0 ^ (n + 1) * beta_1 ^ n * ... * beta_n ^ 1`.

The recurrence is the finite weighted-Motzkin encoding of the displayed
Jacobi fraction: level steps carry weight `alpha`, up-down pairs carry
weight `beta`. The product over `Finset.range n` with shift `beta (j + 1)`
and exponent `n - j` gives `beta (j + 1)` the exponents `n, ..., 1`.
No nonzero `beta` hypothesis is needed.

## Depends on

- [Hankel Transform](../../../../../NumberTheory/MathlibExt/part-06/hankel-transform/hankel-transform.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.HeilermannWeightedMotzkinDeterminant](../../../../../../sources/v2/MathlibExt.md)
- Paul Barry, *From Fibonacci to Robbins: Series Reversion and Hankel Transforms*, Journal of Integer Sequences 24 (2021), Article 21.10.2, lines 110–117, https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex; source SHA-256 `9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`; normalized line-span SHA-256 `a838e5996f223ba9e45347f17ad864912efc392f5c3d56ea749bcf62d3289825`; concept `jis_dep_heilermann_049f63eb`; grounded ID `jis_grounded_049f63eb8aadf7377777a597`.
