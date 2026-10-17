---
article_id: af_61fee718d47baefdecfb1f26
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.PicardIterationWanted.picard_iterates_step_estimate
---

# Picard iterates step estimate

Picard step estimate: successive iterates differ by at most
`M * L^n * |t - t₀|^(n+1) / (n+1)!`.

Proof: Induct on the iterate index, apply the Lipschitz bound under the interval integral, and
integrate the absolute-power majorant exactly, as in the induction for estimate (2.29) in the proof
of Teschl, Theorem 2.5 (Section 2.3).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.PicardIteration](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entries `Picard method` and `rate of convergence and estimation of error` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.3.
