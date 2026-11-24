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
# Identity, composition, and adjoint laws for the scalar-right correspondence

The canonical complete-Hilbert correspondence preserves the three basic
operator operations needed by Hilbert-module and Fredholm consumers.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace InnerProduct RightActions

namespace ScalarRight.Adjointable

noncomputable section

universe u v w

@[simp]
theorem ofContinuousLinearMap_id
    (H : Type u)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    ofContinuousLinearMap H H (ContinuousLinearMap.id ℂ H) =
      CStarModule.AdjointableOperator.id (B := ℂ) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  apply CStarModule.AdjointableOperator.ext
  intro x
  apply (equivL H).injective
  rw [ofContinuousLinearMap_apply,
    CStarModule.AdjointableOperator.id_apply,
    ContinuousLinearMap.id_apply]

@[simp]
theorem ofContinuousLinearMap_comp
    (H : Type u) (K : Type v) (L : Type w)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
    (S : K →L[ℂ] L) (T : H →L[ℂ] K) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
    let _ : NormedAddCommGroup (ScalarRight L) := instNormedAddCommGroup L
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : Module ℂ (ScalarRight K) := instComplexModule K
    let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
    let _ : Module ℂ (ScalarRight L) := instComplexModule L
    let _ : NormedSpace ℂ (ScalarRight L) := instNormedSpace L
    let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
    let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
    let _ : SMul ℂᵐᵒᵖ (ScalarRight L) := instOppositeSMul L
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
    let _ : CStarModule ℂᵐᵒᵖ (ScalarRight L) := cStarModule L
    ofContinuousLinearMap H L (S.comp T) =
      (ofContinuousLinearMap K L S).comp
        (ofContinuousLinearMap H K T) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : NormedAddCommGroup (ScalarRight L) := instNormedAddCommGroup L
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  let _ : Module ℂ (ScalarRight L) := instComplexModule L
  let _ : NormedSpace ℂ (ScalarRight L) := instNormedSpace L
  let _ : SMul ℂᵐᵒᵖ (ScalarRight H) := instOppositeSMul H
  let _ : SMul ℂᵐᵒᵖ (ScalarRight K) := instOppositeSMul K
  let _ : SMul ℂᵐᵒᵖ (ScalarRight L) := instOppositeSMul L
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight H) := cStarModule H
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight K) := cStarModule K
  let _ : CStarModule ℂᵐᵒᵖ (ScalarRight L) := cStarModule L
  apply CStarModule.AdjointableOperator.ext
  intro x
  apply (equivL L).injective
  rw [ofContinuousLinearMap_apply,
    CStarModule.AdjointableOperator.comp_apply,
    ofContinuousLinearMap_apply, ofContinuousLinearMap_apply,
    ContinuousLinearMap.comp_apply]

@[simp]
theorem ofContinuousLinearMap_adjointOperator
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K) :
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
    (ofContinuousLinearMap H K T).adjointOperator =
      ofContinuousLinearMap K H (ContinuousLinearMap.adjoint T) := by
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
  apply CStarModule.AdjointableOperator.ext
  intro y
  apply (equivL H).injective
  have hAdj :
      (ofContinuousLinearMap H K T).adjoint =
        continuousLinearMap K H (ContinuousLinearMap.adjoint T) :=
    ofContinuousLinearMap_adjoint H K T
  have hAdjPoint :
      equivL H ((ofContinuousLinearMap H K T).adjoint y) =
        equivL H
          (continuousLinearMap K H (ContinuousLinearMap.adjoint T) y) :=
    congrArg
      (fun f : ScalarRight K →L[ℂ] ScalarRight H => equivL H (f y)) hAdj
  calc
    equivL H ((ofContinuousLinearMap H K T).adjointOperator y) =
        equivL H ((ofContinuousLinearMap H K T).adjoint y) := rfl
    _ = equivL H
        (continuousLinearMap K H (ContinuousLinearMap.adjoint T) y) :=
      hAdjPoint
    _ = ContinuousLinearMap.adjoint T (equivL K y) :=
      continuousLinearMap_apply K H (ContinuousLinearMap.adjoint T) y
    _ = equivL H
        (ofContinuousLinearMap K H (ContinuousLinearMap.adjoint T) y) :=
      (ofContinuousLinearMap_apply K H
        (ContinuousLinearMap.adjoint T) y).symm

end
end ScalarRight.Adjointable
