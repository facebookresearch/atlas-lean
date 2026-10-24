---
article_id: af_6d4772a6be103234c9660c82
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ward_sbinomial_carry_product_general
---

# Ward sbinomial carry product general

Ward's identity with hypotheses only on positive indices: if `f k = ∏_{d ∣ k} s d` and
`s b ≠ 0` for all positive `k` and `b`, then the `f`-factorial quotient
`f!(n + m) / (f!(n) f!(m))` equals `wardGeneralizedBinomialCoefficient s n m`.
`ward_sbinomial_carry_product` is the source-shaped form.

## Depends on

- [Ward Generalized Binomial Coefficient](../../../../Combinatorics/MathlibExt/part-01/enumerative/part-09/ward-generalized-binomial/ward-generalized-binomial-coefficient.md)

## Proof depends on

- [Ward Generalized Binomial Coefficient eq prod Icc](../../../../Combinatorics/MathlibExt/part-01/enumerative/part-09/ward-generalized-binomial/ward-generalized-binomial-coefficient-eq.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.WardSBinomialCarryProduct](../../../../../sources/v2/MathlibExt.md)
