---
article_id: af_ee4049e3914b304a57707c8a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bAryBinomialCoefficient_eq_prod_div_pow
---

# B Ary Binomial Coefficient eq prod div pow

`bAryBinomialCoefficient b n k hb` is the product over positions `i < L` of the binomial
coefficients of the base-`b` digits `n / b ^ i % b` and `k / b ^ i % b`, for any `L` with
`n < b ^ L` and `k < b ^ L`.

## Depends on

- [B Ary Binomial Coefficient](../bary-binomial-coefficient/b-ary-binomial-coefficient.md)

## Proof depends on

- [B Ary Binomial Coefficient eq prod get D](../bary-binomial-coefficient/b-ary-binomial-coefficient-eq-prod-get-d.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BAryBinomialSymmetryPascal](../../../../../../../sources/v2/MathlibExt.md)
