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

public import MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight.Adjointable
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Ordinary Hilbert-space operators as scalar-right adjointable operators

On complete complex inner-product spaces, Mathlib supplies the canonical
adjoint of every bounded complex-linear map. This module specializes the
pair-based ScalarRight bridge and packages the resulting carrier
correspondence. The noncomplete pair-based API remains the lower layer.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace InnerProduct RightActions

namespace ScalarRight.Adjointable

noncomputable section

universe u v

/-- The canonical ScalarRight adjointable operator attached to an ordinary
bounded operator between complex Hilbert spaces. -/
noncomputable def ofContinuousLinearMap
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
    CStarModule.AdjointableOperator ℂ (ScalarRight H) (ScalarRight K) :=
  ofOrdinaryAdjointPair H K T (ContinuousLinearMap.adjoint T) fun x y =>
    (ContinuousLinearMap.adjoint_inner_right T x y).symm

/-- Forget the ScalarRight model by conjugating the forward action through the
factory continuous-linear equivalences. -/
noncomputable def toContinuousLinearMap
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
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
    H →L[ℂ] K := by
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
  exact (equivL K).toContinuousLinearMap.comp
    (T.toContinuousLinearMap.comp (equivL H).symm.toContinuousLinearMap)

@[simp]
theorem ofContinuousLinearMap_apply
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : H →L[ℂ] K) (x : ScalarRight H) :
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
    equivL K (ofContinuousLinearMap H K T x) = T (equivL H x) :=
  ofOrdinaryAdjointPair_apply H K T (ContinuousLinearMap.adjoint T)
    (fun a b => (ContinuousLinearMap.adjoint_inner_right T a b).symm) x

@[simp]
theorem ofContinuousLinearMap_adjoint
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
    (ofContinuousLinearMap H K T).adjoint =
      continuousLinearMap K H (ContinuousLinearMap.adjoint T) :=
  ofOrdinaryAdjointPair_adjoint H K T (ContinuousLinearMap.adjoint T)
    fun a b => (ContinuousLinearMap.adjoint_inner_right T a b).symm

@[simp]
theorem toContinuousLinearMap_apply
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
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
      CStarModule.AdjointableOperator ℂ (ScalarRight H) (ScalarRight K))
    (x : H) :
    toContinuousLinearMap H K T x =
      equivL K (T ((equivL H).symm x)) :=
  rfl

/-- On complete complex Hilbert spaces, ordinary bounded operators correspond
exactly to adjointable operators on the factory-equipped ScalarRight models. -/
noncomputable def continuousLinearMapEquiv
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
    (H →L[ℂ] K) ≃
      CStarModule.AdjointableOperator ℂ (ScalarRight H) (ScalarRight K) := by
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
  exact {
    toFun := ofContinuousLinearMap H K
    invFun := toContinuousLinearMap H K
    left_inv := by
      intro T
      ext x
      change equivL K
          (ofContinuousLinearMap H K T ((equivL H).symm x)) = T x
      rw [ofContinuousLinearMap_apply, (equivL H).apply_symm_apply]
    right_inv := by
      intro T
      apply CStarModule.AdjointableOperator.ext
      intro x
      apply (equivL K).injective
      rw [ofContinuousLinearMap_apply, toContinuousLinearMap_apply,
        (equivL H).symm_apply_apply] }

end
end ScalarRight.Adjointable
