---
article_id: af_ecd681cb760a79bc1c40fddf
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bAryBinomialCoefficient_generating_function
---

# B Ary Binomial Coefficient generating function

The generating function over `k` of the `b`-ary binomial coefficients
`bAryBinomialCoefficient b n k` factors over the base-`b` digits `n_l` of `n` as
`∏_l (1 + x^(b^l))^(n_l)`, over any commutative semiring.

## Depends on

- [B Ary Binomial Coefficient](../bary-binomial-coefficient/b-ary-binomial-coefficient.md)

## Proof depends on

- [B Ary Binomial Coefficient eq prod get D](../bary-binomial-coefficient/b-ary-binomial-coefficient-eq-prod-get-d.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BAryBinomialGeneratingFunction](../../../../../../../sources/v2/MathlibExt.md)
- Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem (equation eq:barybinomialgeneratingfunction), lines 322–329, https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
