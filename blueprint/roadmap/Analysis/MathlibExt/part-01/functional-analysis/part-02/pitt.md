---
article_id: af_c8573a0e10826576ae901433
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.PittWanted.pitt
---

# Pitt

For `1 ≤ q < p < ∞` and `𝕜 = ℝ` or `ℂ`, every bounded linear operator `T : lp (fun _ : ℕ => 𝕜) p
→L[𝕜] lp (fun _ : ℕ => 𝕜) q` from `ℓ^p(ℕ, 𝕜)` to `ℓ^q(ℕ, 𝕜)` is compact. Source: H. R. Pitt,
A Note on Bilinear Forms, J. London Math. Soc. s1-11 (1936), 174–180,
DOI 10.1112/JLMS/S1-11.3.174, compactness of operators `ℓ^p → ℓ^q` for `q<p`; textbook Albiac
and Kalton, Topics in Banach Space Theory Prop 2.1.6; Lean states `RCLike` `lp _ p →L[𝕜] lp _ q`
with `q<p<∞` compact specialization via `IsCompactOperator`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.Pitt](../../../../../../sources/v2/MathlibExt.md)
