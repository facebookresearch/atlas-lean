---
article_id: af_019459f9330f8519741b99b6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Convex.KarushKuhnTucker.karush_kuhn_tucker_inequality
---

# Karush Kuhn Tucker

Inequality-only KKT necessary conditions in a finite-dimensional real normed
space: if `x` is feasible for finitely many differentiable inequality
constraints, locally minimizes `f` on the feasible set, and LICQ holds at `x`
for the active constraints, then there exist nonneg multipliers `lam` with
complementarity and stationarity
`fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Convex.KarushKuhnTucker](../../../../../sources/v2/MathlibExt.md)
- W. Karush, Minima of Functions of Several Variables with Inequalities as Side Conditions (M.Sc. thesis, Univ. Chicago, 1939); H. W. Kuhn and A. W. Tucker, Nonlinear Programming, Proc. Second Berkeley Symposium (1951), 481–492, DOI 10.1525/9780520411586-036.
