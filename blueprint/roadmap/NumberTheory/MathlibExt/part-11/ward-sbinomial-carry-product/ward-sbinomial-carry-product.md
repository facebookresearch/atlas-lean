---
article_id: af_a1a347bbf618e14227f0f16e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ward_sbinomial_carry_product
---

# Ward sbinomial carry product

Generalized Ward identity for `f`-binomial coefficients via ones-position carries.

Math notes: `(n % b + m % b) / b` is the carry in the ones position when adding `n`
and `m` in base `b`; for the classical case this recovers Kummer's carry-count theorem.
It follows from `ward_sbinomial_carry_product_general` and
`wardGeneralizedBinomialCoefficient_eq_prod_Icc`; the hypotheses `hs` and `hf` are used only at
positive indices.
Proves `Wanted` entry `ward_sbinomial_carry_product`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ward Generalized Binomial Coefficient](../../../../Combinatorics/MathlibExt/part-01/enumerative/part-09/ward-generalized-binomial/ward-generalized-binomial-coefficient.md)
- [Ward Generalized Binomial Coefficient eq prod Icc](../../../../Combinatorics/MathlibExt/part-01/enumerative/part-09/ward-generalized-binomial/ward-generalized-binomial-coefficient-eq.md)
- [Ward sbinomial carry product general](ward-sbinomial-carry-product-general.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.WardSBinomialCarryProduct](../../../../../sources/v2/MathlibExt.md)
- Tom Edgar and Michael Z. Spivey, "Multiplicative Functions, Generalized Binomial Coefficients, and Generalized Catalan Numbers," Journal of Integer Sequences 19 (2016), Article 16.1.6, Theorem [Ward] `thmward` (equation `wardeqn`), lines 475–482, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex>; attributed there to M. Ward.
