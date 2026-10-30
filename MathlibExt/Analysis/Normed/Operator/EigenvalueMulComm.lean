/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import MathlibExt.LinearAlgebra.Eigenspace.MulComm

@[expose] public section

/-!
# Nonzero eigenvalues of a product of bounded operators, in either order

For bounded operators `S T : E →L[𝕜] E`, the nonzero eigenvalues of `S * T`
and of `T * S` coincide, with the same geometric multiplicity. Generalized
eigenspaces have equal `Module.finrank` at every exponent and are
finite-dimensional together. This is the bounded-operator form of the linear-map statements
in `MathlibExt.LinearAlgebra.Eigenspace.MulComm`, obtained by coercing the
products to endomorphisms.

As a corollary, `T† * T` and `T * T†` have the same nonzero eigenvalues on a
Hilbert space.

Eigenvalues here are stated for the underlying endomorphisms
`((S * T : E →L[𝕜] E) : Module.End 𝕜 E)`, matching the convention used in
Mathlib's Fredholm alternative for compact operators.

## Main declarations

* `ContinuousLinearMap.hasEigenvalue_mul_iff`: nonzero eigenvalue transfer for
  `S * T` vs `T * S`.
* `ContinuousLinearMap.finrank_eigenspace_mul_eq`: equal geometric
  multiplicities for bounded operators.
* `ContinuousLinearMap.finrank_genEigenspace_mul_eq`: equal finranks of
  generalized eigenspaces for bounded operators.
* `ContinuousLinearMap.finite_genEigenspace_mul_iff`: finite-dimensionality
  parity for generalized eigenspaces of bounded operators.
* `ContinuousLinearMap.hasEigenvalue_adjoint_mul_self_iff`: nonzero
  eigenvalues of `T† * T` vs `T * T†`.
-/

namespace MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {S T : E →L[𝕜] E} {μ : 𝕜}

/-- A nonzero scalar is an eigenvalue of `S * T` iff it is an eigenvalue of
`T * S`, for bounded operators. -/
theorem hasEigenvalue_mul_iff (S T : E →L[𝕜] E) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue ((S * T : E →L[𝕜] E) : Module.End 𝕜 E) μ ↔
      Module.End.HasEigenvalue ((T * S : E →L[𝕜] E) : Module.End 𝕜 E) μ := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul]
  exact MathlibExt.LinearAlgebra.Eigenspace.MulComm.End.hasEigenvalue_mul_iff
    (S : Module.End 𝕜 E) (T : Module.End 𝕜 E) hμ

/-- The geometric multiplicities of a nonzero eigenvalue of `S * T` and of
`T * S` agree, for bounded operators. -/
theorem finrank_eigenspace_mul_eq (S T : E →L[𝕜] E) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.finrank 𝕜
        (Module.End.eigenspace ((S * T : E →L[𝕜] E) : Module.End 𝕜 E) μ) =
      Module.finrank 𝕜
        (Module.End.eigenspace ((T * S : E →L[𝕜] E) : Module.End 𝕜 E) μ) := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul]
  exact MathlibExt.LinearAlgebra.Eigenspace.MulComm.End.finrank_eigenspace_mul_eq
    (S : Module.End 𝕜 E) (T : Module.End 𝕜 E) hμ

/-- The generalized `μ`-eigenspaces of `S * T` and of `T * S` have equal
`Module.finrank`, for every exponent `k : ℕ∞`, for bounded operators. -/
theorem finrank_genEigenspace_mul_eq (S T : E →L[𝕜] E) {μ : 𝕜} (hμ : μ ≠ 0)
    (k : ℕ∞) :
    Module.finrank 𝕜
        (Module.End.genEigenspace ((S * T : E →L[𝕜] E) : Module.End 𝕜 E) μ k) =
      Module.finrank 𝕜
        (Module.End.genEigenspace ((T * S : E →L[𝕜] E) : Module.End 𝕜 E) μ k) := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul]
  exact MathlibExt.LinearAlgebra.Eigenspace.MulComm.End.finrank_genEigenspace_mul_eq
    (S : Module.End 𝕜 E) (T : Module.End 𝕜 E) hμ k

/-- Generalized eigenspaces of reversed bounded-operator products are
finite-dimensional together for a nonzero scalar and every exponent. -/
theorem finite_genEigenspace_mul_iff (S T : E →L[𝕜] E) {μ : 𝕜} (hμ : μ ≠ 0)
    (k : ℕ∞) :
    Module.Finite 𝕜
        (Module.End.genEigenspace ((S * T : E →L[𝕜] E) : Module.End 𝕜 E) μ k) ↔
      Module.Finite 𝕜
        (Module.End.genEigenspace ((T * S : E →L[𝕜] E) : Module.End 𝕜 E) μ k) := by
  rw [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_mul]
  exact MathlibExt.LinearAlgebra.Eigenspace.MulComm.End.finite_genEigenspace_mul_iff
    (S : Module.End 𝕜 E) (T : Module.End 𝕜 E) hμ k

/-- A nonzero scalar is an eigenvalue of `T† * T` iff it is an eigenvalue of
`T * T†`, on a Hilbert space. -/
theorem hasEigenvalue_adjoint_mul_self_iff {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (T : E →L[𝕜] E) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue
        ((ContinuousLinearMap.adjoint T * T : E →L[𝕜] E) : Module.End 𝕜 E) μ ↔
      Module.End.HasEigenvalue
        ((T * ContinuousLinearMap.adjoint T : E →L[𝕜] E) : Module.End 𝕜 E) μ :=
  hasEigenvalue_mul_iff (ContinuousLinearMap.adjoint T) T hμ

end ContinuousLinearMap

end MathlibExt.Analysis.Normed.Operator.EigenvalueMulComm
