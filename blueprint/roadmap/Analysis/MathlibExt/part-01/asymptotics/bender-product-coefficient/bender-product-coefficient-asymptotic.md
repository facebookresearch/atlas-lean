---
article_id: af_ad65bc1e25afb433fa3ae7b4
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Asymptotics.BenderProductCoefficient.bender_product_coefficient_asymptotic
---

# Bender product coefficient asymptotic

Bender's product-coefficient asymptotic lemma: for real power series `A` of radius `α`
and `B` of radius `β < α`, if consecutive coefficient ratios of `B` tend to `β` and
`A` is nonzero at `β`, then the coefficients of `A * B` are asymptotically `A(β) * b n`.

The eventual-nonzero hypothesis `hbnz` is a soundness repair, not a strengthening: the
displayed quotients `b (n-1) / b n` presuppose defined denominators, but Lean totalizes
division by zero. Without it the statement is false at `β = 0`: with `A(z) = 1 + z`,
`b` vanishing on every even index and growing fast on odd indices makes every totalized
ratio zero while the even product coefficients stay nonzero. Natural subtraction in
`n - 1` changes only the initial term and is harmless at `atTop`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Bender product coefficient asymptotic general](bender-product-coefficient-asymptotic-ge.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Asymptotics.BenderProductCoefficient](../../../../../../sources/v2/MathlibExt.md)
- Dennis E. Davenport, Louis W. Shapiro, Lara K. Pudwell, and Leon C. Woodson, "The Boundary of Ordered Trees," Journal of Integer Sequences 18 (2015). Source file: `https://cs.uwaterloo.ca/journals/JIS/VOL18/Davenport/dav3.tex` (Bender's lemma, lines 521-523). File SHA-256: `32a240baaed6ae2300ec1302ccf7d3cd50dc1976868c161f0029c77d0d43b845`. Span SHA-256 (LF joining, no terminal LF): `665087b645846d87aadb08ae26e311b6d717dd5340e113e601cacab26f1c0d85`. Concept: `jis_grounded_6fda7dab32c4f4ae24158c9e` (dependency `jis_dep_2479eb9e033e69c0a770ff11`). It follows from `bender_product_coefficient_asymptotic_general`; the hypothesis `hB` is unused and keeps the source's shape. Proves `Wanted` entry `bender_product_coefficient_asymptotic`.
