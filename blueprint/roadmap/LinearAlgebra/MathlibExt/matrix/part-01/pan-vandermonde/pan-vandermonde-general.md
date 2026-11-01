---
article_id: af_33de6ad74e4c8c0ef132fb5a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pan_vandermonde_general
---

# Pan vandermonde general

The generalized factorial matrix `(∏ j < r, (x c - j * α))_{r,c}` on distinct nodes `x`
factors as the matrix of `S α β γ` times the generalized factorial matrix with nodes shifted by
`γ` and step `β`, has the Vandermonde determinant `∏_{i < j} (x j - x i)`, is invertible, and
has inverse `V⁻¹ * S 0 α 0`, where `V` is the same matrix with `α = 0`. This holds in every
dimension `p`, including `p = 0`. `pan_vandermonde` is the source-shaped form.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.PanVandermonde](../../../../../../sources/v2/MathlibExt.md)
