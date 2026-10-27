---
article_id: af_800929f93d528af59339a252
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrixWanted.fundamental_matrix_liouville_det
---

# Fundamental matrix liouville det

Liouville (Abel) formula: the Wronskian determinant of a fundamental
matrix grows by the exponential of the integrated trace.

Proof: Jacobi's formula follows from the determinant's first-order term; an integrating factor then
gives Teschl, Lemma 3.11, formula (3.91).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Det of mul](det-of-mul.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.ODE.LinearSystemFundamentalMatrix](../../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential equations`, entry `linear differential systems` (unmapped); G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.4; stable ref https://en.wikipedia.org/wiki/Abel%27s_identity.
