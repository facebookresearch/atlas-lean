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
# Hilbert-space operators and right scalar-module operators

For complex Hilbert spaces `H,K`, put `qH = equivL H` and `qK = equivL K`, identifying
`ScalarRight H` with `H` and `ScalarRight K` with `K`. Every bounded complex-linear operator `T
: H →L[ℂ] K` has a Hilbert adjoint; transporting this pair gives the adjointable operator
`qK.symm ∘ T ∘ qH`.

Conversely an adjointable operator `S` between these right scalar modules gives `qK ∘ S ∘
qH.symm`. The two constructions are inverse. The latter construction is also defined for
incomplete complex inner-product spaces.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace InnerProduct RightActions

namespace ScalarRight.Adjointable

noncomputable section

universe u v

/-- **Hilbert operator as a right-module operator.** For complex Hilbert spaces `H,K` and `T : H
→L[ℂ] K`, put `qH = equivL H : ScalarRight H ≃L[ℂ] H` and `qK = equivL K : ScalarRight K ≃L[ℂ]
K`. Transporting `T` and its Hilbert adjoint gives the adjointable map `qK.symm ∘ T ∘ qH`. -/
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

/-- **Bounded map underlying a scalar-module operator.** For complex inner-product spaces `H,K`,
let `qH = equivL H : ScalarRight H ≃L[ℂ] H` and `qK = equivL K : ScalarRight K ≃L[ℂ] K`. An
adjointable map `S : ScalarRight H → ScalarRight K` gives `qK ∘ S ∘ qH.symm : H →L[ℂ] K`. This
direction does not require completeness. -/
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

/-- **Hilbert-to-module operator correspondence.** For complex Hilbert spaces `H,K`, bounded
complex-linear maps `H →L[ℂ] K` correspond bijectively to adjointable maps between
`ScalarRight H` and `ScalarRight K`; the forward map is `ofContinuousLinearMap` and the
inverse is `toContinuousLinearMap`. -/
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
