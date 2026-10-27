---
article_id: af_5fdd26bfda2ac8fdfb277c27
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.WeierstrassFactorizationWanted.weierstrass_factorization
---

# Weierstrass Factorization

Every closed discrete `S ⊆ ℂ` (isolated by punctured balls) is the exact zero set of some entire
`f : ℂ → ℂ` with simple zeros: `∀ z, f z = 0 ↔ z ∈ S` and `∀ z ∈ S, deriv f z ≠ 0`. Source:
Weierstrass factorization theorem 1876; see Rudin; Lean is simple-zero corollary with closed
discrete prescribed zero set S and entire f with exact zeros S and nonvanishing derivative on S.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.WeierstrassFactorization](../../../../../../sources/v2/MathlibExt.md)
