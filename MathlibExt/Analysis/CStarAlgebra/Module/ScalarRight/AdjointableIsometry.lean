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

public import MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight.AdjointableEquiv

/-!
# The scalar-right adjointable correspondence is a linear isometry

The complete-Hilbert carrier equivalence is upgraded to a complex-linear
isometric equivalence. The proof uses the exact ScalarRight factories and
operator norms; no compactness or Calkin assertion is made here.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace InnerProduct RightActions

namespace ScalarRight.Adjointable

noncomputable section

universe u v

theorem ofContinuousLinearMap_toContinuousLinearMap
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
    (ofContinuousLinearMap H K T).toContinuousLinearMap =
      continuousLinearMap H K T :=
  ofOrdinaryAdjointPair_toContinuousLinearMap H K T
    (ContinuousLinearMap.adjoint T)
    (fun x y => (ContinuousLinearMap.adjoint_inner_right T x y).symm)

/-- Conjugation through the fixed ScalarRight equivalences preserves the
operator norm. Completeness is not needed. -/
theorem norm_continuousLinearMap
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
    let _ : AddCommMonoid (ScalarRight H) :=
      (instNormedAddCommGroup H).toAddCommMonoid
    let _ : AddCommMonoid (ScalarRight K) :=
      (instNormedAddCommGroup K).toAddCommMonoid
    let _ : UniformSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace
    let _ : UniformSpace (ScalarRight K) :=
      (instNormedAddCommGroup K).toUniformSpace
    let _ : TopologicalSpace (ScalarRight H) :=
      (instNormedAddCommGroup H).toUniformSpace.toTopologicalSpace
    let _ : TopologicalSpace (ScalarRight K) :=
      (instNormedAddCommGroup K).toUniformSpace.toTopologicalSpace
    let _ : Module ℂ (ScalarRight H) := (instNormedSpace H).toModule
    let _ : Module ℂ (ScalarRight K) := (instNormedSpace K).toModule
    let T' : ScalarRight H →L[ℂ] ScalarRight K := by
      exact continuousLinearMap H K T
    ‖T'‖ = ‖T‖ := by
  let _ : NormedAddCommGroup (ScalarRight H) := instNormedAddCommGroup H
  let _ : NormedAddCommGroup (ScalarRight K) := instNormedAddCommGroup K
  let _ : Module ℂ (ScalarRight H) := instComplexModule H
  let _ : NormedSpace ℂ (ScalarRight H) := instNormedSpace H
  let _ : Module ℂ (ScalarRight K) := instComplexModule K
  let _ : NormedSpace ℂ (ScalarRight K) := instNormedSpace K
  let _ : AddCommMonoid (ScalarRight H) :=
    (instNormedAddCommGroup H).toAddCommMonoid
  let _ : AddCommMonoid (ScalarRight K) :=
    (instNormedAddCommGroup K).toAddCommMonoid
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : UniformSpace (ScalarRight K) :=
    (instNormedAddCommGroup K).toUniformSpace
  let _ : TopologicalSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace.toTopologicalSpace
  let _ : TopologicalSpace (ScalarRight K) :=
    (instNormedAddCommGroup K).toUniformSpace.toTopologicalSpace
  let _ : Module ℂ (ScalarRight H) := (instNormedSpace H).toModule
  let _ : Module ℂ (ScalarRight K) := (instNormedSpace K).toModule
  let T' : ScalarRight H →L[ℂ] ScalarRight K := by
    exact continuousLinearMap H K T
  let eH : ScalarRight H ≃ₗᵢ[ℂ] H :=
    { toLinearEquiv := by exact (equivL H).toLinearEquiv
      norm_map' := fun x =>
        (isometry_equivL H).norm_map_of_map_zero
          (map_zero (equivL H)) x }
  let eK : ScalarRight K ≃ₗᵢ[ℂ] K :=
    { toLinearEquiv := by exact (equivL K).toLinearEquiv
      norm_map' := fun x =>
        (isometry_equivL K).norm_map_of_map_zero
          (map_zero (equivL K)) x }
  change ‖(eK.symm : K →L[ℂ] ScalarRight K).comp
      (T.comp (eH : ScalarRight H →L[ℂ] H))‖ = ‖T‖
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

theorem norm_ofContinuousLinearMap
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
    ‖ofContinuousLinearMap H K T‖ = ‖T‖ := by
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
  let _ : AddCommMonoid (ScalarRight H) :=
    (instNormedAddCommGroup H).toAddCommMonoid
  let _ : AddCommMonoid (ScalarRight K) :=
    (instNormedAddCommGroup K).toAddCommMonoid
  let _ : UniformSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace
  let _ : UniformSpace (ScalarRight K) :=
    (instNormedAddCommGroup K).toUniformSpace
  let _ : TopologicalSpace (ScalarRight H) :=
    (instNormedAddCommGroup H).toUniformSpace.toTopologicalSpace
  let _ : TopologicalSpace (ScalarRight K) :=
    (instNormedAddCommGroup K).toUniformSpace.toTopologicalSpace
  let _ : Module ℂ (ScalarRight H) := (instNormedSpace H).toModule
  let _ : Module ℂ (ScalarRight K) := (instNormedSpace K).toModule
  let T' : ScalarRight H →L[ℂ] ScalarRight K := by
    exact continuousLinearMap H K T
  have hT' (x : ScalarRight H) :
      equivL K (T' x) = T (equivL H x) := by
    change equivL K (continuousLinearMap H K T x) = T (equivL H x)
    exact continuousLinearMap_apply H K T x
  have hforward :
      (ofContinuousLinearMap H K T).toContinuousLinearMap = T' := by
    apply ContinuousLinearMap.ext
    intro x
    apply (equivL K).injective
    change equivL K (ofContinuousLinearMap H K T x) = equivL K (T' x)
    exact (ofContinuousLinearMap_apply H K T x).trans (hT' x).symm
  rw [CStarModule.AdjointableOperator.norm_eq, hforward]
  exact norm_continuousLinearMap H K T

/-- The complete-Hilbert scalar-right correspondence as a complex-linear
equivalence. -/
noncomputable def continuousLinearMapLinearEquiv
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
    (H →L[ℂ] K) ≃ₗ[ℂ]
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
    toEquiv := continuousLinearMapEquiv H K
    map_add' := by
      intro T S
      change ofContinuousLinearMap H K (T + S) =
        ofContinuousLinearMap H K T + ofContinuousLinearMap H K S
      apply CStarModule.AdjointableOperator.ext
      intro x
      apply (equivL K).injective
      simp only [ofContinuousLinearMap_apply,
        CStarModule.AdjointableOperator.add_apply, map_add]
      rfl
    map_smul' := by
      intro c T
      change ofContinuousLinearMap H K (c • T) =
        c • ofContinuousLinearMap H K T
      apply CStarModule.AdjointableOperator.ext
      intro x
      apply (equivL K).injective
      simp only [ofContinuousLinearMap_apply,
        CStarModule.AdjointableOperator.smul_apply, map_smul]
      rfl }

/-- On complete complex Hilbert spaces, bounded operators and scalar-right
adjointable operators are complex-linearly isometrically equivalent. -/
noncomputable def continuousLinearMapLinearIsometryEquiv
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
    (H →L[ℂ] K) ≃ₗᵢ[ℂ]
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
    toLinearEquiv := continuousLinearMapLinearEquiv H K
    norm_map' := norm_ofContinuousLinearMap H K }

end
end ScalarRight.Adjointable
