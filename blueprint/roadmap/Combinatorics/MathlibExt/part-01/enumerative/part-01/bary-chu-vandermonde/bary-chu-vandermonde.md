---
article_id: af_7e56101476d4c9f9bdcd6aa9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.bary_chu_vandermonde
---

# Bary chu vandermonde

B-ary Chu-Vandermonde identity under carry-free addition: when the base-`b`
addition of `m` and `n` produces no carries digit by digit, the `b`-ary
binomial coefficient of `m + n` expands as the convolution of the `b`-ary
coefficients of `m` and `n`. The local `C` is the digitwise product of
ordinary binomial coefficients; it agrees with `bAryBinomialCoefficient b x y hb`, so this is
`bAryBinomialCoefficient_chu_vandermonde`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [B Ary Binomial Coefficient](../bary-binomial-coefficient/b-ary-binomial-coefficient.md)
- [B Ary Binomial Coefficient chu vandermonde](b-ary-binomial-coefficient-chu-vandermon.md)
- [B Ary Binomial Coefficient eq prod div pow](../bary-binomial-symmetry-pascal/b-ary-binomial-coefficient-eq-prod-div-p.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BAryChuVandermonde](../../../../../../../sources/v2/MathlibExt.md)
- Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem (equation bChuVandermonde), lines 371–377, https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
