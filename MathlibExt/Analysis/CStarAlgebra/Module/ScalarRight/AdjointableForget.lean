/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight.AdjointableIsometry

/-!
# Forgetting scalar-right adjointable operators is a linear isometry

This is the source-facing orientation of the scalar adjointable
correspondence: module adjointable operators map to ordinary bounded
complex-linear maps. It is the inverse of the canonical-adjoint construction,
not a second carrier or comparison.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace InnerProduct RightActions

namespace ScalarRight.Adjointable

noncomputable section

universe u v

/-- Forget scalar-right adjointable structure by conjugating the forward map
through the fixed ScalarRight equivalences. -/
noncomputable def adjointableOperatorLinearIsometryEquiv
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : Module ℂ (ScalarRight K) := instComplexModule K
    let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
    CStarModule.AdjointableOperator ℂ (ScalarRight H) (ScalarRight K) ≃ₗᵢ[ℂ]
      (H →L[ℂ] K) :=
  (continuousLinearMapLinearIsometryEquiv H K).symm

@[simp]
theorem adjointableOperatorLinearIsometryEquiv_apply
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T :
      let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
      let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
      let _ : Module ℂ (ScalarRight H) := instComplexModule H
      let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
      let _ : Module ℂ (ScalarRight K) := instComplexModule K
      let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
      let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
      let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
      let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
      let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
      CStarModule.AdjointableOperator ℂ (ScalarRight H) (ScalarRight K)) :
    adjointableOperatorLinearIsometryEquiv H K T =
      toContinuousLinearMap H K T :=
  rfl

end
end ScalarRight.Adjointable
