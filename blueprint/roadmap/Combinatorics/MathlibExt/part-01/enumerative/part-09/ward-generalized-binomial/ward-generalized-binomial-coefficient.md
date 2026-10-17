---
article_id: af_14e31b81e2d48d8f98518bef
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.wardGeneralizedBinomialCoefficient
---

# Ward Generalized Binomial Coefficient

Ward's product definition of a generalized binomial coefficient:
`{{n+m} choose n}_s = ∏_{b>1} s_b ^ ε₀^{b,n,m}`.

Only bases at most `n + m` can carry in the units place, so this is a finite product.
The source explicitly uses the product as a definition over arbitrary coefficient
sequences, including sequences with zero terms.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Ward Units Carry](ward-units-carry.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.WardGeneralizedBinomial](../../../../../../../sources/v2/MathlibExt.md)
