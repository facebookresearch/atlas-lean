---
article_id: af_6f3a0417c7bb356aad36a042
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.moment_generating_function_as_J_fraction_general
---

# Moment generating function as J fraction general

Moment generating function as a J-fraction, assuming only what the argument uses: if `p`
satisfies the three-term recurrence with coefficients `α` and `β`, `μ k = L (X ^ k)`, and
`L (p n) = 0` for `n ≥ 1`, then the moments have a Jacobi fraction
`HasJacobiFraction μ α β (μ 0) S` whose tails `S n` have constant coefficient one.
`moment_generating_function_as_J_fraction` is the source-shaped form.

## Depends on

- [Has Jacobi Fraction](../../../../NumberTheory/MathlibExt/part-06/hankel-transform/has-jacobi-fraction.md)

## Sources

- [MathlibExt, MathlibExt.Algebra.Polynomial.MomentGeneratingJFraction](../../../../../sources/v2/MathlibExt.md)
