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
public import MathlibExt.Analysis.CStarAlgebra.Module.Compact

/-!
# Rank-one operators on right scalar modules

For complex inner-product spaces `H,K`, the module rank-one operator `z ↦ x <• rightInner y z`
becomes the Hilbert-space operator `z ↦ ⟪equivL H y, z⟫_ℂ • equivL K x` under scalar-module
identification.

On complete spaces the inverse correspondence sends a Hilbert-space rank-one operator to this
module rank-one operator, and hence into the complex span of module rank-one operators.
-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace InnerProduct RightActions

namespace ScalarRight.Adjointable

noncomputable section

universe u v

/-- **Hilbert-space form of a module rank-one operator.** For complex inner-product spaces,
forgetting the module rank-one map defined by `x,y` gives `InnerProductSpace.rankOne ℂ (equivL
K x) (equivL H y)`. Completeness is not required. -/
theorem toContinuousLinearMap_rankOne
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (x : ScalarRight K) (y : ScalarRight H) :
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
    toContinuousLinearMap H K
        (CStarModule.AdjointableOperator.rankOne (B := ℂ) x y) =
      InnerProductSpace.rankOne ℂ (equivL K x) (equivL H y) := by
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
  ext z
  change equivL K
      (CStarModule.AdjointableOperator.rankOne (B := ℂ) x y
        ((equivL H).symm z)) =
    InnerProductSpace.rankOne ℂ (equivL K x) (equivL H y) z
  rw [CStarModule.AdjointableOperator.rankOne_apply,
    ScalarRight.right_smul_apply, ScalarRight.rightInner_apply,
    (equivL H).apply_symm_apply, InnerProductSpace.rankOne_apply]

/-- **Module form of a Hilbert rank-one operator.** For complex Hilbert spaces and `x : K`, `y :
H`, the image of `InnerProductSpace.rankOne ℂ x y` is the module rank-one operator defined by
`(equivL K).symm x` and `(equivL H).symm y`. -/
theorem ofContinuousLinearMap_rankOne
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (x : K) (y : H) :
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
    ofContinuousLinearMap H K (InnerProductSpace.rankOne ℂ x y) =
      CStarModule.AdjointableOperator.rankOne (B := ℂ)
        ((equivL K).symm x) ((equivL H).symm y) := by
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
  intro z
  apply (equivL K).injective
  rw [ofContinuousLinearMap_apply, InnerProductSpace.rankOne_apply,
    CStarModule.AdjointableOperator.rankOne_apply,
    ScalarRight.right_smul_apply, ScalarRight.rightInner_apply,
    (equivL K).apply_symm_apply, (equivL H).apply_symm_apply]

/-- **Rank-one images in the module finite-rank span.** For complex Hilbert spaces,
`ofContinuousLinearMap H K (InnerProductSpace.rankOne ℂ x y)` lies in the module finite-rank
submodule. -/
theorem ofContinuousLinearMap_rankOne_mem_finiteRank
    (H : Type u) (K : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (x : K) (y : H) :
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
    ofContinuousLinearMap H K (InnerProductSpace.rankOne ℂ x y) ∈
      CStarModule.AdjointableOperator.finiteRankSubmodule
        (B := ℂ) (E := ScalarRight H) (F := ScalarRight K) := by
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
  rw [ofContinuousLinearMap_rankOne]
  exact CStarModule.AdjointableOperator.rankOne_mem_finiteRank
    ((equivL K).symm x) ((equivL H).symm y)

end
end ScalarRight.Adjointable
