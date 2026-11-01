---
article_id: af_64b6a00e09b537c083ea8483
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bAryBinomialCoefficient_chu_vandermonde
---

# B Ary Binomial Coefficient chu vandermonde

Chu-Vandermonde identity for `b`-ary binomial coefficients: when `m` and `n` add without
carries in base `b`, `bAryBinomialCoefficient b (m + n) r hb` is the convolution of the `b`-ary
binomial coefficients of `m` and `n`.

## Depends on

- [B Ary Binomial Coefficient](../bary-binomial-coefficient/b-ary-binomial-coefficient.md)

## Proof depends on

- [B Ary Binomial Coefficient eq prod div pow](../bary-binomial-symmetry-pascal/b-ary-binomial-coefficient-eq-prod-div-p.md)
- [B Ary Binomial Coefficient generating function](../bary-binomial-generating-function/b-ary-binomial-coefficient-generating-fu.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BAryChuVandermonde](../../../../../../../sources/v2/MathlibExt.md)
