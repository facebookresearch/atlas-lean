---
article_id: af_ae7dfc171858bc4d2b2709ca
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.ramanujanTheta_summable
---

# Ramanujan Summability

Ramanujan's general theta series absolute convergence (arXiv:2607.26471,
`Oliver_identities.tex` ll. 127-130): `f(a,b)=∑_{n:ℤ} a^{n(n+1)/2} b^{n(n-1)/2}`
with `|a*b|<1`. The summand is `MetaMathlibExt.ramanujanThetaTerm` (triangular
exponents via `Int.toNat`); this is the absolute-summability theorem over `ℝ`.

## Depends on

- [Ramanujan Theta Term](ramanujan/ramanujan-theta-term.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability](../../../../../../sources/v2/MathlibExt.md)
