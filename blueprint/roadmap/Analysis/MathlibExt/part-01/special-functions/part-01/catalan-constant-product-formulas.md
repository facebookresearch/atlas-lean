---
article_id: af_4bfc138b9e9e325d3421c1db
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.catalan_constant_product_formulas
---

# Catalan Constant Products

Three infinite product formulas for exponentials of Catalan's constant
`G`: `exp (2 * G / π - 1 / 2)` and `exp (2 * G / π + 1 / 2)` as limits of
`∏_{n=1}^{2m}` and `∏_{n=1}^{2m+1}` of `(1 - 2 / (2n+1)) ^ (n * (-1)^n)`,
and `exp (4 * G / π)` as the limit of the squared quotient of
`(4k+3)^(4k+3)` over `(4k+1)^(4k+1)` products with the boundary factor
`(4m+3)^(2m+1) / (4m+1)^(6m+1)`, with `G` specified by its alternating
reciprocal-squares series.

The products over `Finset.range m` of `(4k+3)^(4k+3)` and `(4k+1)^(4k+1)`
are the source's `3^3 · 7^7 ⋯ (4m-1)^(4m-1)` and
`1^1 · 5^5 ⋯ (4m-3)^(4m-3)`. All three limits were confirmed numerically
(first two to ~1e-12 at `m = 200000`, the third to ~5e-7 via a
cancellation-free reformulation).

Proof: Following Kachi and Tzermias, Proposition (catalan), dominated convergence reduces the
product limit to the cosecant integral. The substitutions `x = πu/2` and `x = 2 arctan t`, followed
by the arctangent power series, evaluate it in terms of `G`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.CatalanConstantProducts](../../../../../../sources/v2/MathlibExt.md)
- Yasuyuki Kachi and Pavlos Tzermias, "Infinite Products Involving ζ(3) and Catalan's Constant," Journal of Integer Sequences 15 (2012), Article 12.9.4, Proposition (label catalan), equations (labels catalani, catalanii, catalaniii), lines 147–165, https://cs.uwaterloo.ca/journals/JIS/VOL15/Tzermias/tzermias2.tex
