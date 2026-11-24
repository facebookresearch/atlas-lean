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

public import MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.OfPair

/-!
# Ordinary Hilbert-space adjoint pairs on the scalar-right model

An ordinary bounded complex-linear map and a supplied ordinary adjoint are
transported through the exact `ScalarRight.equivL` factories and bundled as the
existing C-star-module `AdjointableOperator`. No canonical adjoint choice,
completeness, global instance or parallel operator carrier is introduced.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace RightActions

namespace ScalarRight.Adjointable

noncomputable section

universe u v

/-- Transport an ordinary bounded complex-linear map to the two explicitly
factory-equipped scalar-right models. -/
noncomputable def continuousLinearMap
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : H →L[ℂ] K) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : Module ℂ (ScalarRight K) := instComplexModule K
    let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
    ScalarRight H →L[ℂ] ScalarRight K := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  exact (equivL K).symm.toContinuousLinearMap.comp
    (T.comp (equivL H).toContinuousLinearMap)

@[simp]
theorem continuousLinearMap_apply
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : H →L[ℂ] K) (x : ScalarRight H) :
    let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
    let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
    let _ : Module ℂ (ScalarRight H) := instComplexModule H
    let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
    let _ : Module ℂ (ScalarRight K) := instComplexModule K
    let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
    equivL K (continuousLinearMap H K T x) = T (equivL H x) := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  change equivL K ((equivL K).symm (T (equivL H x))) = T (equivL H x)
  exact (equivL K).apply_symm_apply _

/-- Bundle an ordinary bounded adjoint pair on `H,K` as an adjointable
operator between their exact scalar-right models. The source convention is
conjugate-linear first and linear second. -/
noncomputable def ofOrdinaryAdjointPair
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (S : K →L[ℂ] H)
    (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ) :
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
  let T' : ScalarRight H →L[ℂ] ScalarRight K :=
    (equivL K).symm.toContinuousLinearMap.comp
      (T.comp (equivL H).toContinuousLinearMap)
  let S' : ScalarRight K →L[ℂ] ScalarRight H :=
    (equivL H).symm.toContinuousLinearMap.comp
      (S.comp (equivL K).toContinuousLinearMap)
  exact CStarModule.AdjointableOperator.ofAdjointPair T' S' (by
    intro x y
    rw [ScalarRight.rightInner_apply, ScalarRight.rightInner_apply]
    change ⟪T (equivL H x), equivL K y⟫_ℂ =
      ⟪equivL H x, S (equivL K y)⟫_ℂ
    exact h _ _)

@[simp]
theorem ofOrdinaryAdjointPair_toContinuousLinearMap
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (S : K →L[ℂ] H)
    (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ) :
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
    (ofOrdinaryAdjointPair H K T S h).toContinuousLinearMap =
      continuousLinearMap H K T := by
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
  let T' : ScalarRight H →L[ℂ] ScalarRight K :=
    (equivL K).symm.toContinuousLinearMap.comp
      (T.comp (equivL H).toContinuousLinearMap)
  let S' : ScalarRight K →L[ℂ] ScalarRight H :=
    (equivL H).symm.toContinuousLinearMap.comp
      (S.comp (equivL K).toContinuousLinearMap)
  have h' : ∀ x y,
      CStarModule.rightInner (B := ℂ) (T' x) y =
        CStarModule.rightInner (B := ℂ) x (S' y) := by
    intro x y
    rw [ScalarRight.rightInner_apply, ScalarRight.rightInner_apply]
    change ⟪T (equivL H x), equivL K y⟫_ℂ =
      ⟪equivL H x, S (equivL K y)⟫_ℂ
    exact h _ _
  change (CStarModule.AdjointableOperator.ofAdjointPair T' S' h').toContinuousLinearMap =
    T'
  exact CStarModule.AdjointableOperator.ofAdjointPair_toContinuousLinearMap
    T' S' h'

@[simp]
theorem ofOrdinaryAdjointPair_adjoint
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (S : K →L[ℂ] H)
    (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ) :
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
    (ofOrdinaryAdjointPair H K T S h).adjoint =
      continuousLinearMap K H S := by
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
  let T' : ScalarRight H →L[ℂ] ScalarRight K :=
    (equivL K).symm.toContinuousLinearMap.comp
      (T.comp (equivL H).toContinuousLinearMap)
  let S' : ScalarRight K →L[ℂ] ScalarRight H :=
    (equivL H).symm.toContinuousLinearMap.comp
      (S.comp (equivL K).toContinuousLinearMap)
  have h' : ∀ x y,
      CStarModule.rightInner (B := ℂ) (T' x) y =
        CStarModule.rightInner (B := ℂ) x (S' y) := by
    intro x y
    rw [ScalarRight.rightInner_apply, ScalarRight.rightInner_apply]
    change ⟪T (equivL H x), equivL K y⟫_ℂ =
      ⟪equivL H x, S (equivL K y)⟫_ℂ
    exact h _ _
  change (CStarModule.AdjointableOperator.ofAdjointPair T' S' h').adjoint =
    S'
  exact CStarModule.AdjointableOperator.ofAdjointPair_adjoint T' S' h'

@[simp]
theorem ofOrdinaryAdjointPair_apply
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (T : H →L[ℂ] K) (S : K →L[ℂ] H)
    (h : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ)
    (x : ScalarRight H) :
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
    equivL K (ofOrdinaryAdjointPair H K T S h x) = T (equivL H x) := by
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
  have hforward :
      (ofOrdinaryAdjointPair H K T S h).toContinuousLinearMap =
        continuousLinearMap H K T :=
    ofOrdinaryAdjointPair_toContinuousLinearMap H K T S h
  calc
    equivL K (ofOrdinaryAdjointPair H K T S h x) =
        equivL K (continuousLinearMap H K T x) :=
      congrArg (fun f : ScalarRight H →L[ℂ] ScalarRight K =>
        equivL K (f x)) hforward
    _ = T (equivL H x) := continuousLinearMap_apply H K T x

end
end ScalarRight.Adjointable
