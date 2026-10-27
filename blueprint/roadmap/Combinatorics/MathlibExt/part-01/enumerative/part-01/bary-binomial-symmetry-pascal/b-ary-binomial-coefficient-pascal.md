---
article_id: af_bee9be3bc3924692ce4545f0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bAryBinomialCoefficient_pascal
---

# B Ary Binomial Coefficient pascal

The `b`-ary binomial coefficients satisfy Pascal's recurrence where they are nonzero:
`C_b(n, k) = C_b(n - 1, k - 1) + C_b(n - 1, k)` for `0 < k ≤ n` and `C_b(n, k) ≠ 0`.

## Depends on

- [B Ary Binomial Coefficient](../bary-binomial-coefficient/b-ary-binomial-coefficient.md)

## Proof depends on

- [B Ary Binomial Coefficient eq prod div pow](b-ary-binomial-coefficient-eq-prod-div-p.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BAryBinomialSymmetryPascal](../../../../../../../sources/v2/MathlibExt.md)
