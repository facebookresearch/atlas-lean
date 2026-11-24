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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.InducedCompletion

import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The original pure cross norm of the actual compact tensor action

Original pure-vector norms and the actual action formula give a joint bound
on the Hilbert operator and coefficient left multiplication. Two weighted
operator-norm bounds recover the product of the two original norms without
division or a nonzero-space assumption. The C-star regular norm of the genuine
coefficient left multiplier supplies its original coefficient norm.

The exact induced source gauge and canonical completed source image therefore
have the original pure cross norm. This is one needed field of the genuine
cross-norm data; raw injectivity and equality with the least cross norm remain
separate minimum bridges, and terminal Takai/equivariance proofs stay open.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions TensorProduct Topology
open CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]

/-- The actual elementary tensor compact-action norm is the product of the two original norms. -/
theorem norm_algebraicCompactTensorHom_tmul (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A;
    ‖algebraicCompactTensorHom H A (a ⊗ₜ[ℂ] T)‖ = ‖a‖ * ‖T‖ := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  let : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  let : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  let : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  let : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  let P : AdjointableOperator.End A (Space H A) :=
    (algebraicCompactTensorHom H A (a ⊗ₜ[ℂ] T) : AdjointableOperator.End A (Space H A))
  have hP : P = coefficientHom H A a * compactHilbertHom H A T := by
    change (algebraicCompactTensorHom H A (a ⊗ₜ[ℂ] T) :
      AdjointableOperator.End A (Space H A)) = coefficientHom H A a * compactHilbertHom H A T
    rw [algebraicCompactTensorHom_tmul]
    rfl
  have ha : ‖coefficientHom H A a‖ ≤ ‖a‖ := coefficientOperator_norm_le H A a
  have hT : ‖compactHilbertHom H A T‖ ≤ ‖T‖ := compactHilbertHom_norm_le H A T
  have hupper : ‖P‖ ≤ ‖a‖ * ‖T‖ := by
    rw [hP]
    exact (norm_mul_le _ _).trans
      (mul_le_mul ha hT (_root_.norm_nonneg _) (_root_.norm_nonneg _))
  have hpoint (ξ : H) (b : A) :
      ‖(T : H →L[ℂ] H) ξ‖ * ‖a * b‖ ≤ ‖P‖ * (‖ξ‖ * ‖b‖) := by
    have haction : P (pure H A ξ b) = pure H A ((T : H →L[ℂ] H) ξ) (a * b) :=
      algebraicCompactTensorHom_pure H A a T ξ b
    calc
      ‖(T : H →L[ℂ] H) ξ‖ * ‖a * b‖ = ‖P (pure H A ξ b)‖ := by
        rw [haction, norm_pure]
      _ ≤ ‖P‖ * ‖pure H A ξ b‖ := by
        rw [AdjointableOperator.norm_eq]
        exact P.toContinuousLinearMap.le_opNorm (pure H A ξ b)
      _ = ‖P‖ * (‖ξ‖ * ‖b‖) := by rw [norm_pure]
  have hleft (ξ : H) : ‖(T : H →L[ℂ] H) ξ‖ * ‖a‖ ≤ ‖P‖ * ‖ξ‖ := by
    let L : A →L[ℂ] A :=
      (‖(T : H →L[ℂ] H) ξ‖ : ℂ) • ContinuousLinearMap.mul ℂ A a
    have hL : ‖L‖ ≤ ‖P‖ * ‖ξ‖ := by
      apply ContinuousLinearMap.opNorm_le_bound L
        (mul_nonneg (_root_.norm_nonneg P) (_root_.norm_nonneg ξ))
      intro b
      calc
        ‖L b‖ = ‖(T : H →L[ℂ] H) ξ‖ * ‖a * b‖ := by
          change ‖(‖(T : H →L[ℂ] H) ξ‖ : ℂ) • (a * b)‖ =
            ‖(T : H →L[ℂ] H) ξ‖ * ‖a * b‖
          rw [norm_smul, Complex.norm_of_nonneg (_root_.norm_nonneg _)]
        _ ≤ (‖P‖ * ‖ξ‖) * ‖b‖ := by simpa only [mul_assoc] using hpoint ξ b
    have hnormL : ‖L‖ = ‖(T : H →L[ℂ] H) ξ‖ * ‖a‖ := by
      change ‖(‖(T : H →L[ℂ] H) ξ‖ : ℂ) • ContinuousLinearMap.mul ℂ A a‖ =
        ‖(T : H →L[ℂ] H) ξ‖ * ‖a‖
      rw [norm_smul, Complex.norm_of_nonneg (_root_.norm_nonneg _),
        ContinuousLinearMap.opNorm_mul_apply]
    exact hnormL.symm.trans_le hL
  let U : H →L[ℂ] H := (‖a‖ : ℂ) • (T : H →L[ℂ] H)
  have hU : ‖U‖ ≤ ‖P‖ := by
    apply ContinuousLinearMap.opNorm_le_bound U (_root_.norm_nonneg P)
    intro ξ
    calc
      ‖U ξ‖ = ‖a‖ * ‖(T : H →L[ℂ] H) ξ‖ := by
        change ‖(‖a‖ : ℂ) • ((T : H →L[ℂ] H) ξ)‖ = ‖a‖ * ‖(T : H →L[ℂ] H) ξ‖
        rw [norm_smul, Complex.norm_of_nonneg (_root_.norm_nonneg _)]
      _ ≤ ‖P‖ * ‖ξ‖ := by simpa only [mul_comm] using hleft ξ
  have hnormU : ‖U‖ = ‖a‖ * ‖T‖ := by
    change ‖(‖a‖ : ℂ) • (T : H →L[ℂ] H)‖ = ‖a‖ * ‖T‖
    have hnormT : ‖(T : H →L[ℂ] H)‖ = ‖T‖ :=
      Submodule.norm_coe (s := (compactEndomorphismClosedStarIdeal (H := H)).carrier.toSubmodule) T
    rw [norm_smul, Complex.norm_of_nonneg (_root_.norm_nonneg _), hnormT]
  have hlower : ‖a‖ * ‖T‖ ≤ ‖P‖ := hnormU.symm.trans_le hU
  change ‖P‖ = ‖a‖ * ‖T‖
  exact le_antisymm hupper hlower

/-- The actual induced C-star seminorm retains the original elementary cross-norm equation. -/
theorem compactTensorSeminorm_tmul (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    compactTensorSeminorm H A (a ⊗ₜ[ℂ] T) = ‖a‖ * ‖T‖ := by
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (compactTensorSeminorm_apply H A (a ⊗ₜ[ℂ] T)).trans
    (norm_algebraicCompactTensorHom_tmul H A a T)

/-- The actual canonical completion image has the original product norm on every pure tensor. -/
theorem norm_toCompactTensorCompletion_tmul (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A;
    ‖toCompactTensorCompletion H A (a ⊗ₜ[ℂ] T)‖ = ‖a‖ * ‖T‖ := by
  let : NonUnitalCStarAlgebra (CompactTensorCompletion H A) := compactTensorCompletionCStarAlgebra H A
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  exact (norm_toCompactTensorCompletion H A (a ⊗ₜ[ℂ] T)).trans
    (norm_algebraicCompactTensorHom_tmul H A a T)

end

end CStarModule.HilbertAmplification
