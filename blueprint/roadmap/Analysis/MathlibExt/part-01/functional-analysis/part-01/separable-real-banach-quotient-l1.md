---
article_id: af_bc3d784abaa951351420a8c5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.L1Quotient.separableRealBanach_quotient_l1
---

# L1 Quotient

Every separable real Banach space `E` is a continuous linear quotient of `ℓ¹(ℕ, ℝ)`: there exists
`T : lp (fun _ : ℕ => ℝ) 1 →L[ℝ] E` surjective. Source: S. Banach, Theorie des operations
lineaires, 1932, `ℓ¹` quotient theorem; Albiac and Kalton, Topics in Banach Space Theory; Lean
states separable real Banach specialization with concrete `lp _ 1` domain and surjective bounded
linear quotient.
Proves `Wanted` entry `separableRealBanach_quotient_l1`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.L1Quotient](../../../../../../sources/v2/MathlibExt.md)
