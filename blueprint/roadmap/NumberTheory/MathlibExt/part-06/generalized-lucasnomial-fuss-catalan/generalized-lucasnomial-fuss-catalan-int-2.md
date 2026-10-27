---
article_id: af_1bc5c330ace4a249ab897dde
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalized_lucasnomial_fuss_catalan_integral
---

# Generalized lucasnomial fuss catalan integral

The generalized Lucasnomial Fuss-Catalan numbers `U_r / U_{(a-1)*n+r} * C(an+r-1,n)_U` are
integral for all `n ≥ 1`. Source: Christian Ballot, "Lucasnomial Fuss-Catalan Numbers and Related
Divisibility Questions," Journal of Integer Sequences 21 (2018), Article 18.6.5, Theorem `thm:2`,
lines 553–558, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Ballot/ballot30.tex>. Fundamental Lucas
sequences, nondegeneracy, and regularity at lines 185–207; Lucasnomial coefficients at lines
215–221.
It follows from `generalized_lucasnomial_fuss_catalan_integral_general`; the hypotheses `hP` and
`hQ` are unused and keep the source's shape.
Proves `Wanted` entry `generalized_lucasnomial_fuss_catalan_integral`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Generalized lucasnomial fuss catalan integral general](generalized-lucasnomial-fuss-catalan-int.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GeneralizedLucasnomialFussCatalan](../../../../../sources/v2/MathlibExt.md)
