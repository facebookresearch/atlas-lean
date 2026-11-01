---
article_id: af_930db62a1b260607cf424d45
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.base_digits_binomial_generating_function
---

# Base digits binomial generating function

The generating function over `k` of the `b`-ary binomial coefficients of `n`
(products of digitwise binomial coefficients) factors as the stated product
over base-`b` digits.

The `b`-ary coefficient is the product over the `Nat.digits b n` positions of
`choose` of the `n`/`k` digits (zero-padded via `getD`); the right side is the
product of `(1 + x^(b^l))^(n_l)`. Verified computationally as a polynomial
identity for `b ∈ {2, 3, 5, 10}` and `n ∈ {0, 1, 2, 5, 7, 13, 19, 29}`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [B Ary Binomial Coefficient](../bary-binomial-coefficient/b-ary-binomial-coefficient.md)
- [B Ary Binomial Coefficient eq prod get D](../bary-binomial-coefficient/b-ary-binomial-coefficient-eq-prod-get-d.md)
- [B Ary Binomial Coefficient generating function](b-ary-binomial-coefficient-generating-fu.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.BAryBinomialGeneratingFunction](../../../../../../../sources/v2/MathlibExt.md)
- Lin Jiu and Christophe Vignat, "On Binomial Identities in Arbitrary Bases," Journal of Integer Sequences 19 (2016), Article 16.5.5, Theorem (equation eq:barybinomialgeneratingfunction), lines 322–329, https://cs.uwaterloo.ca/journals/JIS/VOL19/Jiu/jiu4.tex
