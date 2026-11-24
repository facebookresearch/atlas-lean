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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.ScalarRepresentation
public import MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
import Mathlib.Tactic.Ring

/-!
# The actual Hilbert amplification of a nonunital coefficient algebra

The carrier is the literal balanced internal tensor completion of the original
complex Hilbert space with the coefficient self module. Its norm, complex
module, coefficient action and inner product are the existing radical and stock
completion data. Compact endomorphisms retain that actual operator norm.

This construction does not identify the compact algebra with a minimum tensor
until the genuine elementary action and norm/density comparison are supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions
open CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]

/-- The original Hilbert space internally tensored over ℂ with the coefficient
self module, through the actual balancing/radical quotients and completion. -/
abbrev Space : Type (max uH uA) := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  exact CompletedTensor (E₁ := ScalarRight H) (scalarSelfHom A)

/-- The existing radical norm followed by its stock completion norm. -/
@[instance_reducible]
def spaceNormedAddCommGroup : NormedAddCommGroup (Space H A) := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  letI : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  exact inferInstanceAs
    (NormedAddCommGroup (CompletedTensor (E₁ := ScalarRight H) (scalarSelfHom A)))

/-- The stock completed complex module and norm, with their exact group data. -/
@[instance_reducible]
def spaceNormedSpace :
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    NormedSpace ℂ (Space H A) := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  letI : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  exact inferInstanceAs
    (NormedSpace ℂ (CompletedTensor (E₁ := ScalarRight H) (scalarSelfHom A)))

/-- The original descended right coefficient action extended by stock completion. -/
@[instance_reducible]
def spaceOppositeSMul : SMul Aᵐᵒᵖ (Space H A) := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  letI : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  exact inferInstanceAs
    (SMul Aᵐᵒᵖ (CompletedTensor (E₁ := ScalarRight H) (scalarSelfHom A)))

/-- The existing completed coefficient-valued inner product with the fixed
stock norm, complex module and coefficient action. -/
@[instance_reducible]
def spaceCStarModule :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    CStarModule Aᵐᵒᵖ (Space H A) := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  letI : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  exact completedCStarModule (E₁ := ScalarRight H) (scalarSelfHom A)

/-- The original pure Hilbert/coefficient tensor on the actual completion. -/
def pure (ξ : H) (a : A) : Space H A := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  letI : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  exact completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) a

/-- The original coefficient-valued pure-tensor inner formula. -/
theorem rightInner_pure (ξ η : H) (a b : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    rightInner (B := A) (pure H A ξ a) (pure H A η b) =
      inner ℂ ξ η • (star a * b) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  have : @CompleteSpace (ScalarRight H)
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
  have hscalar (c : ℂ) (x : A) : scalarSelfHom A c x = c • x := rfl
  have hinner : rightInner (B := ℂ) ((ScalarRight.equivL H).symm ξ)
      ((ScalarRight.equivL H).symm η) = inner ℂ ξ η := by
    rw [ScalarRight.rightInner_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  change rightInner (B := A)
      (completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) a)
      (completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm η) b) = _
  rw [rightInner_completedPure, hinner, hscalar, CStarModule.Right.rightInner_self,
    mul_smul_comm]

/-- The computed pure norm is the product of the original two factor norms. -/
theorem norm_pure (ξ : H) (a : A) :
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    ‖pure H A ξ a‖ = ‖ξ‖ * ‖a‖ := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  let : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  let : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  let : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  let : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  have : @CompleteSpace (ScalarRight H)
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
  apply (sq_eq_sq₀ (norm_nonneg (pure H A ξ a))
    (mul_nonneg (norm_nonneg ξ) (norm_nonneg a))).mp
  rw [← CStarModule.norm_rightInner_self (B := A), rightInner_pure,
    norm_smul, ← inner_self_re_eq_norm, inner_self_eq_norm_sq,
    CStarRing.norm_star_mul_self]
  ring

/-- The actual norm-closed compact endomorphisms of the original amplification. -/
abbrev CompactAlgebra : Type (max uH uA) := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  letI : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact ↥(AdjointableOperator.CompactEnd A (Space H A))

/-- The explicit existing closed-ideal C-star dictionary on the actual compact
endomorphism carrier. No global norm or algebra instance is registered. -/
@[instance_reducible]
def compactCStarAlgebra : NonUnitalCStarAlgebra (CompactAlgebra H A) := by
  letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  letI : NormedAddCommGroup (ScalarRight H) := ScalarRight.instNormedAddCommGroup H
  letI : Module ℂ (ScalarRight H) := ScalarRight.instComplexModule H
  letI : NormedSpace ℂ (ScalarRight H) := ScalarRight.instNormedSpace H
  letI : SMul ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.instOppositeSMul H
  letI : @CompleteSpace (ScalarRight H)
      (ScalarRight.instNormedAddCommGroup H).toUniformSpace := by
    rw [ScalarRight.normedAddCommGroup_uniformSpace]
    exact (ScalarRight.completeSpace_iff H).mpr inferInstance
  letI : CStarModule ℂᵐᵒᵖ (ScalarRight H) := ScalarRight.cStarModule H
  letI : NormedAddCommGroup (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedAddCommGroup (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedSpace ℂ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalTensorNormedSpace (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : SMul Aᵐᵒᵖ (RadicalTensor (E₁ := ScalarRight H) (scalarSelfHom A)) :=
    radicalRightAction (E₁ := ScalarRight H) (scalarSelfHom A)
  letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact (AdjointableOperator.compactClosedStarIdeal (B := A) (E := Space H A)).carrierCStarAlgebra

end

end CStarModule.HilbertAmplification
