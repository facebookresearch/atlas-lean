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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.HilbertAction
public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.CoefficientHom
public import MathlibExt.Analysis.CStarAlgebra.Operator.Calkin

/-!
# Hilbert operator representation on amplification

For a complex Hilbert space `H` and nonunital C-star algebra `A`, the first-factor operators
`D_T (ξ⊗a) = (T ξ)⊗a` give a nonunital complex star-algebra homomorphism `B(H) → End_A(Space H
A)` with `‖D_T‖ ≤ ‖T‖`. Its restriction to the closed ideal `K(H)` of compact Hilbert-space
operators has the same action and norm bound.

The restricted Hilbert action commutes with the coefficient representation `L_a`, enabling the
two factors in the algebraic tensor representation. The elementary coefficient/compact products
are treated separately.
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

/-- **Hilbert operator star representation.** For complex Hilbert `H` and nonunital `A`,
`hilbertHom H A` sends `T ∈ B(H)` to `D_T : ξ⊗a ↦ (T ξ)⊗a`, preserving multiplication and the
Hilbert adjoint. -/
def hilbertHom :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    (H →L[ℂ] H) →⋆ₙₐ[ℂ] AdjointableOperator.End A (Space H A) := by
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
  exact
    { toFun := hilbertOperator H A
      map_zero' := by
        apply operator_ext_pure H A
        intro ξ b
        rw [hilbertOperator_pure, zero_apply, AdjointableOperator.zero_apply]
        change completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm 0) b = 0
        simp only [map_zero, completedPure, balancedPure_zero_left]
      map_add' := fun T S => by
        apply operator_ext_pure H A
        intro ξ b
        rw [hilbertOperator_pure, AdjointableOperator.add_apply,
          hilbertOperator_pure, hilbertOperator_pure, add_apply]
        change completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (T ξ + S ξ)) b =
          completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (T ξ)) b +
            completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (S ξ)) b
        rw [map_add]
        exact completedPure_add_left (scalarSelfHom A)
          ((ScalarRight.equivL H).symm (T ξ)) ((ScalarRight.equivL H).symm (S ξ)) b
      map_mul' := fun T S => by
        apply operator_ext_pure H A
        intro ξ b
        rw [hilbertOperator_pure, AdjointableOperator.mul_apply,
          hilbertOperator_pure, hilbertOperator_pure]
        rfl
      map_smul' := fun c T => by
        apply operator_ext_pure H A
        intro ξ b
        rw [hilbertOperator_pure, AdjointableOperator.smul_apply,
          hilbertOperator_pure, smul_apply]
        change completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (c • T ξ)) b =
          c • completedPure (scalarSelfHom A) ((ScalarRight.equivL H).symm (T ξ)) b
        rw [map_smul]
        exact completedPure_smul_left (scalarSelfHom A) c ((ScalarRight.equivL H).symm (T ξ)) b
      map_star' := fun T => by
        apply operator_ext_pure H A
        intro ξ b
        rw [hilbertOperator_pure, AdjointableOperator.star_apply,
          hilbertOperator_adjoint_pure, ContinuousLinearMap.star_eq_adjoint] }

/-- **Value of the Hilbert representation.** `hilbertHom H A T = hilbertOperator H A T` for a
bounded operator `T` on `H`. -/
@[simp]
theorem hilbertHom_apply (T : H →L[ℂ] H) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    hilbertHom H A T = hilbertOperator H A T := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  rfl

/-- **Hilbert representation on pure vectors.** `hilbertHom H A T (pure H A ξ b) = pure H A (T ξ)
b`. -/
theorem hilbertHom_pure (T : H →L[ℂ] H) (ξ : H) (b : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    hilbertHom H A T (pure H A ξ b) = pure H A (T ξ) b := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact hilbertOperator_pure H A T ξ b

/-- **Contractive Hilbert operator representation.** `‖hilbertHom H A T‖ ≤ ‖T‖` in the
amplification operator norm. -/
theorem hilbertHom_norm_le (T : H →L[ℂ] H) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    ‖hilbertHom H A T‖ ≤ ‖T‖ := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact hilbertOperator_norm_le H A T

/-- **Restriction to compact Hilbert operators.** Restrict `hilbertHom H A` to `K(H)`, obtaining a
star-algebra map into the adjointable endomorphisms of `Space H A`. -/
def compactHilbertHom :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    (compactEndomorphismClosedStarIdeal (H := H)).carrier →⋆ₙₐ[ℂ]
      AdjointableOperator.End A (Space H A) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact (hilbertHom H A).comp
    (NonUnitalStarSubalgebraClass.subtype (R := ℂ)
      (compactEndomorphismClosedStarIdeal (H := H)).carrier)

/-- **Value of the compact Hilbert representation.** For `T ∈ K(H)`, `compactHilbertHom H A T =
hilbertOperator H A T` after inclusion into bounded Hilbert operators. -/
@[simp]
theorem compactHilbertHom_apply
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    compactHilbertHom H A T = hilbertOperator H A (T : H →L[ℂ] H) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  rfl

/-- **Compact Hilbert action on pure vectors.** For a compact `T`, `compactHilbertHom H A T (pure
ξ b) = pure (T ξ) b`. -/
theorem compactHilbertHom_pure
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) (ξ : H) (b : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    compactHilbertHom H A T (pure H A ξ b) =
      pure H A ((T : H →L[ℂ] H) ξ) b := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact hilbertOperator_pure H A (T : H →L[ℂ] H) ξ b

/-- **Norm bound for the compact Hilbert action.** For `T ∈ K(H)`, `‖compactHilbertHom H A T‖ ≤
‖T‖`. -/
theorem compactHilbertHom_norm_le
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    ‖compactHilbertHom H A T‖ ≤ ‖T‖ := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact hilbertOperator_norm_le H A (T : H →L[ℂ] H)

/-- **Commutation of the two tensor representation factors.** For `T ∈ K(H)` and `a : A`,
`compactHilbertHom H A T` commutes with `coefficientHom H A a`. -/
theorem compactHilbertHom_commutes_coefficientHom
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) (a : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    Commute (compactHilbertHom H A T) (coefficientHom H A a) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  exact hilbertOperator_commutes_coefficientOperator H A (T : H →L[ℂ] H) a

end

end CStarModule.HilbertAmplification
