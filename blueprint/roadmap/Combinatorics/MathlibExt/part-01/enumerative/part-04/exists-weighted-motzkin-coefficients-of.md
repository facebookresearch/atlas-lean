---
article_id: af_c5c009e462d699e34445a853
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.exists_weightedMotzkin_coefficients_of_hasJacobiFraction
---

# Heilermann Weighted Motzkin

Algebraic coefficient bridge derived from the Jacobi fraction displayed in
Paul Barry, *From Fibonacci to Robbins: Series Reversion and Hankel Transforms*,
Journal of Integer Sequences 24 (2021), Article 21.10.2, lines 110–117,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Barry2/barry461.tex.
Source SHA-256
`9cd9826f06a6786a792c651fa1f84a8e2bb5b365fb8b57234a78b87714935f51`.
Normalized line-span SHA-256
`a838e5996f223ba9e45347f17ad864912efc392f5c3d56ea749bcf62d3289825`.
Concept `jis_dep_heilermann_049f63eb`.
Grounded `jis_grounded_049f63eb8aadf7377777a597`.

Indexing: the boundary recurrence at height `0` uses `beta 1`, while at height
`j + 1` the down-step contribution uses `beta (j + 2)`.

Barry does not explicitly state this auxiliary tableau lemma; it is a
coefficientwise bridge for the displayed fraction.

## Depends on

- [Has Jacobi Fraction](../../../../../NumberTheory/MathlibExt/part-06/hankel-transform/has-jacobi-fraction.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.HeilermannWeightedMotzkin](../../../../../../sources/v2/MathlibExt.md)
