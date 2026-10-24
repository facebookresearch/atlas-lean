---
article_id: af_fe1454417c467933566825a4
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Dynamics.PointwiseErgodicTheoremsWanted.PointwiseErgodicTheorems.variationalNorm
---

# Variational Norm

We define the `r`-variational norm of a sequence `a : ℕ → ℂ` by
`‖a‖_𝕍ʳ :=`
  `sup_{n ∈ ℕ} |a_n| + sup_{J ∈ ℕ} sup_{N_0 ≤ … ≤ N_J} (∑_j^{J-1} |a_{N_{j+1}} - a_{N_j}|^r)^{1/r}`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Dynamics.PointwiseErgodicTheoremsWanted](../../../../sources/v2/WantedExt.md)
