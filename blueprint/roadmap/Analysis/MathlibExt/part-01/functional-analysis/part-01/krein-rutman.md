---
article_id: af_f38c9b8eb6a53acbd6882496
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.KreinRutmanWanted.krein_rutman
---

# Krein Rutman

For compact Hausdorff `K`, if `T : C(K, ℝ) →L[ℝ] C(K, ℝ)` is compact, positive (`f ≥ 0 → T f ≥ 0`
pointwise), and has `0 < spectralRadius ℝ T`, then there exists nonzero `f ≥ 0` with `T f =
(spectralRadius ℝ T).toReal • f`. Source: M. G. Krein and M. A. Rutman,
Linear operators leaving invariant a cone in a Banach space,
Uspekhi Mat. Nauk 3 (1948), 1–95, positive compact operator principal eigenvalue; Deimling,
Nonlinear Functional Analysis; Lean states `C(K, ℝ)` compact positive case with spectralRadius
eigenvector and nonnegativity.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.KreinRutman](../../../../../../sources/v2/MathlibExt.md)
