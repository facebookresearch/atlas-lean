---
article_id: af_e453de7a18b3c7b700c78891
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.WeierstrassPreparationWanted.weierstrass_preparation
---

# Weierstrass Preparation

Let `E` be finite-dimensional over `ℂ`, `f : E × ℂ → ℂ` analytic at `0` with `f (0, w)=w^d g w`
near `0` for analytic `g`, `g 0 ≠ 0`. Then near `0`, `f p = u p * (p.2^d + ∑ j, a_j p.1 *
p.2^(j:ℕ))` for analytic `a_j : E → ℂ`, `a_j 0=0` and unit `u`, `u 0≠0`. Source: Weierstrass
preparation theorem in several complex variables; see Hörmander; Lean is finite-dimensional E × ℂ
product form, order d slice factorization w^d g w, Weierstrass polynomial with vanishing
coefficients and unit u, local open U, fixed field ℂ specialization.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.WeierstrassPreparation](../../../../../../sources/v2/MathlibExt.md)
