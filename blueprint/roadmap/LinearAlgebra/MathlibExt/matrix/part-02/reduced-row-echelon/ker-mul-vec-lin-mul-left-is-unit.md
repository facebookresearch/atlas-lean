---
article_id: af_448db68617b890e85143776c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted.ker_mulVecLin_mul_left_isUnit
---

# Ker mul Vec Lin mul left is Unit

Row operations by an invertible matrix preserve the solution set of the homogeneous system.

Proof: `Matrix.mulVec_mulVec` rewrites `(P * A) *ᵥ x` as `P *ᵥ (A *ᵥ x)`, and `P *ᵥ ·` is
injective because `P` is a unit.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelon](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Matrices / elementary row operations; G. Strang, Introduction to Linear Algebra, 6th ed., Wellesley-Cambridge Press (2023), Section 2.2.
