/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CompactOperatorAdjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

@[expose] public section

open Function Set Filter Topology
open MathlibExt.Analysis.InnerProductSpace.CompactOperatorAdjoint

namespace MathlibExtTest.Analysis.InnerProductSpace.CompactOperatorAdjoint

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Schauder's theorem on an abstract compact operator: the adjoint is
compact. -/
example (T : E →L[𝕜] F) (hc : IsCompactOperator (T : E → F)) :
    IsCompactOperator (ContinuousLinearMap.adjoint T : F → E) :=
  isCompactOperator_adjoint hc

/-- Schauder's theorem, iff form, on an abstract operator. -/
example (T : E →L[𝕜] F) :
    IsCompactOperator (ContinuousLinearMap.adjoint T : F → E) ↔
      IsCompactOperator (T : E → F) :=
  isCompactOperator_adjoint_iff

/-- The adjoint of an abstract finite-rank operator is compact. -/
example {T : E →L[𝕜] F}
    (hT : FiniteDimensional 𝕜 ↥(LinearMap.range (T : E →ₗ[𝕜] F))) :
    IsCompactOperator (ContinuousLinearMap.adjoint T : F → E) :=
  isCompactOperator_adjoint_of_finiteRank hT

/-- The zero operator on an abstract Hilbert space is compact, so its
adjoint is compact. -/
example : IsCompactOperator (ContinuousLinearMap.adjoint
    (0 : E →L[𝕜] E) : E → E) :=
  isCompactOperator_adjoint isCompactOperator_zero

/-- The identity operator on the finite-dimensional space
`EuclideanSpace ℝ (Fin 2)` is compact, so its adjoint is compact. -/
example : IsCompactOperator (ContinuousLinearMap.adjoint
    (1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
  apply isCompactOperator_adjoint
  exact isCompactOperator_id_iff_finiteDimensional (𝕜 := ℝ).mpr inferInstance

/-- The zero operator on `EuclideanSpace ℝ (Fin 2)` is finite-rank, so its
adjoint is compact by the finite-rank lemma directly. -/
example : IsCompactOperator (ContinuousLinearMap.adjoint
    (0 : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
  apply isCompactOperator_adjoint_of_finiteRank
  rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero]
  exact inferInstance

/-- The orthogonal projection onto the span of the first basis vector of
`EuclideanSpace ℝ (Fin 2)` is finite-rank, so its adjoint is compact. -/
example : IsCompactOperator (ContinuousLinearMap.adjoint
    (Submodule.starProjection
      (Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)})) :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
  apply isCompactOperator_adjoint_of_finiteRank
  have hfin : FiniteDimensional ℝ ↥(Submodule.span ℝ
      {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)
  have hle : LinearMap.range
      ((Submodule.starProjection
        (Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)})) :
          EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ≤
        Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)} := by
    rintro y ⟨x, rfl⟩
    simp
  exact Submodule.finiteDimensional_of_le hle

-- Schauder's theorem depends only on the standard axioms.
#print axioms isCompactOperator_adjoint

end MathlibExtTest.Analysis.InnerProductSpace.CompactOperatorAdjoint
