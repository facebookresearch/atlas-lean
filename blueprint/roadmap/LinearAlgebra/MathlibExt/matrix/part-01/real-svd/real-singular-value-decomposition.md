---
article_id: af_b1a3df8b81dfa9faf8c665c5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.RealSVDWanted.real_singular_value_decomposition
---

# Real singular value decomposition

Rectangular real singular value decomposition: every real `m × n` matrix factors as `U * Σ * Vᵀ`
with `U` and `V` orthogonal and `Σ` diagonal with nonnegative entries; the singular values
beyond the first `min m n` (indices `j` with `m ≤ j.val`) are zero.

Proof: Apply the spectral theorem to `AᵀA`, normalize the images of the eigenvectors with positive
eigenvalues, and extend them to an orthonormal basis of the codomain, as in the proof of S. Axler,
Linear Algebra Done Right, 4th ed., 7.70, and the matrix form that follows it (Section 7E).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Exists orthogonal Group rectangular Diagonal antitone](exists-orthogonal-group-rectangular-diag.md)

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.RealSVD](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Numerical Analysis / Iterative methods / singular value decomposition; G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins University Press (2013), Theorem 2.4.1.
