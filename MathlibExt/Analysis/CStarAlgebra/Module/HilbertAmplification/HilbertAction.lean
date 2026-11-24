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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.CoefficientAction
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapLeft.Completion
public import MathlibExt.Analysis.CStarAlgebra.Module.ScalarRight.AdjointableLaws

/-!
# The actual Hilbert-factor action on coefficient amplification

The existing scalar-right correspondence transports an original bounded
Hilbert-space operator and its genuine Hilbert adjoint. The existing completed
first-factor construction acts on the literal Hilbert/coefficient tensor.
Its original pure formula implies commutation with the coefficient action.

These are the two factors needed for the elementary A tensor K(H) operator
in Blackadar, K-Theory for Operator Algebras, Theorem10.1.2. Definition13.5.1
and its following paragraph give the actual internal tensor and first-factor
operator. The minimum tensor norm and the Takai isomorphism remain separate.
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

/-- The original Hilbert operator acts through the actual completed first-factor map. -/
def hilbertOperator (T : H →L[ℂ] H) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    AdjointableOperator.End A (Space H A) := by
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
  exact completedLeftOperator (E₁ := ScalarRight H) (F₁ := ScalarRight H)
    (scalarSelfHom A) (ScalarRight.Adjointable.ofContinuousLinearMap H H T)

/-- The original coefficient stays fixed while its Hilbert vector receives the source operator. -/
@[simp]
theorem hilbertOperator_pure (T : H →L[ℂ] H) (ξ : H) (b : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    hilbertOperator H A T (pure H A ξ b) = pure H A (T ξ) b := by
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
  have hSource : ScalarRight.Adjointable.ofContinuousLinearMap H H T
      ((ScalarRight.equivL H).symm ξ) = (ScalarRight.equivL H).symm (T ξ) := by
    apply (ScalarRight.equivL H).injective
    rw [ScalarRight.Adjointable.ofContinuousLinearMap_apply,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  change completedLeftOperator (E₁ := ScalarRight H) (F₁ := ScalarRight H)
      (scalarSelfHom A) (ScalarRight.Adjointable.ofContinuousLinearMap H H T)
      (completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) b) =
    completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (T ξ)) b
  rw [completedLeftOperator_pure, hSource]

/-- The actual stored adjoint acts through the genuine Hilbert-space adjoint. -/
@[simp]
theorem hilbertOperator_adjoint_pure (T : H →L[ℂ] H) (ξ : H) (b : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    (hilbertOperator H A T).adjoint (pure H A ξ b) =
      pure H A (ContinuousLinearMap.adjoint T ξ) b := by
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
  have hSource : (ScalarRight.Adjointable.ofContinuousLinearMap H H T).adjoint
      ((ScalarRight.equivL H).symm ξ) =
        (ScalarRight.equivL H).symm (ContinuousLinearMap.adjoint T ξ) := by
    apply (ScalarRight.equivL H).injective
    let L : AdjointableOperator.End ℂ (ScalarRight H) :=
      ScalarRight.Adjointable.ofContinuousLinearMap H H T
    let Lstar : AdjointableOperator.End ℂ (ScalarRight H) :=
      ScalarRight.Adjointable.ofContinuousLinearMap H H (ContinuousLinearMap.adjoint T)
    have hLstar : L.adjointOperator = Lstar :=
      ScalarRight.Adjointable.ofContinuousLinearMap_adjointOperator H H T
    have hEq : ScalarRight.equivL H (L.adjointOperator ((ScalarRight.equivL H).symm ξ)) =
        ScalarRight.equivL H ((ScalarRight.equivL H).symm (ContinuousLinearMap.adjoint T ξ)) := by
      calc
        ScalarRight.equivL H (L.adjointOperator ((ScalarRight.equivL H).symm ξ)) =
            ScalarRight.equivL H (Lstar ((ScalarRight.equivL H).symm ξ)) :=
          congrArg (fun S : AdjointableOperator.End ℂ (ScalarRight H) =>
            ScalarRight.equivL H (S ((ScalarRight.equivL H).symm ξ))) hLstar
        _ = ContinuousLinearMap.adjoint T
            (ScalarRight.equivL H ((ScalarRight.equivL H).symm ξ)) :=
          ScalarRight.Adjointable.ofContinuousLinearMap_apply H H
            (ContinuousLinearMap.adjoint T) ((ScalarRight.equivL H).symm ξ)
        _ = ContinuousLinearMap.adjoint T ξ :=
          congrArg (fun v : H => ContinuousLinearMap.adjoint T v)
            ((ScalarRight.equivL H).apply_symm_apply ξ)
        _ = ScalarRight.equivL H
            ((ScalarRight.equivL H).symm (ContinuousLinearMap.adjoint T ξ)) :=
          ((ScalarRight.equivL H).apply_symm_apply _).symm
    simpa only [AdjointableOperator.adjointOperator_apply] using hEq
  change (completedLeftOperator (E₁ := ScalarRight H) (F₁ := ScalarRight H)
      (scalarSelfHom A) (ScalarRight.Adjointable.ofContinuousLinearMap H H T)).adjoint
      (completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm ξ) b) =
    completedPure (scalarSelfHom A)
      ((ScalarRight.equivL H).symm (ContinuousLinearMap.adjoint T ξ)) b
  rw [completedLeftOperator_adjoint_pure, hSource]

/-- The actual completed Hilbert action retains the original Hilbert operator norm bound. -/
theorem hilbertOperator_norm_le (T : H →L[ℂ] H) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    ‖hilbertOperator H A T‖ ≤ ‖T‖ := by
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
  have hBound := completedLeftOperator_norm_le (E₁ := ScalarRight H) (F₁ := ScalarRight H)
    (scalarSelfHom A) (ScalarRight.Adjointable.ofContinuousLinearMap H H T)
  rw [ScalarRight.Adjointable.norm_ofContinuousLinearMap] at hBound
  exact hBound

/-- The two actual completed factor operators commute on the original amplification. -/
theorem hilbertOperator_commutes_coefficientOperator (T : H →L[ℂ] H) (a : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    Commute (hilbertOperator H A T) (coefficientOperator H A a) := by
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
  let L : AdjointableOperator.End A (Space H A) := hilbertOperator H A T
  let R : AdjointableOperator.End A (Space H A) := coefficientOperator H A a
  have hMaps : L.toContinuousLinearMap.comp R.toContinuousLinearMap =
      R.toContinuousLinearMap.comp L.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext_on
      (completedPure_dense_span (E₁ := ScalarRight H) (scalarSelfHom A))
    rintro _ ⟨⟨x, b⟩, rfl⟩
    have hx : completedPure (scalarSelfHom A) x b =
        pure H A (ScalarRight.equivL H x) b := by
      change completedPure (scalarSelfHom A) x b =
        completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (ScalarRight.equivL H x)) b
      rw [ContinuousLinearEquiv.symm_apply_apply]
    change L (R (completedPure (scalarSelfHom A) x b)) =
      R (L (completedPure (scalarSelfHom A) x b))
    rw [hx]
    change hilbertOperator H A T (coefficientOperator H A a
        (pure H A (ScalarRight.equivL H x) b)) =
      coefficientOperator H A a (hilbertOperator H A T
        (pure H A (ScalarRight.equivL H x) b))
    rw [coefficientOperator_pure, hilbertOperator_pure, hilbertOperator_pure, coefficientOperator_pure]
  change L * R = R * L
  apply AdjointableOperator.ext
  intro z
  change (L.toContinuousLinearMap.comp R.toContinuousLinearMap) z =
    (R.toContinuousLinearMap.comp L.toContinuousLinearMap) z
  exact congrArg (fun f : Space H A →L[ℂ] Space H A => f z) hMaps

end

end CStarModule.HilbertAmplification
