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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.CompactImage
public import MathlibExt.Algebra.Star.StarAlgHom
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The actual algebraic A tensor K(full H) star homomorphism

The neutral complex tensor universal map lifts the original bilinear product
of the coefficient and full-H compact factor actions. Their actual commutation
proves multiplication and genuine adjoints prove the star law. The previously
constructed arbitrary compact product puts every original pure tensor in the
actual compact module ideal; linearity gives the whole algebraic tensor image.

The resulting nonunital star-algebra homomorphism has the actual CompactAlgebra
H A target, with original pure formula Txi tensor ab. This is the algebraic
constructor needed for Blackadar10.1.2's original A tensor K(L2G) output. The
spatial minimum completion and terminal Takai theorem remain separate work.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions TensorProduct
open CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]

/-- Lift the literal compact elementary product by the neutral complex tensor universal map. -/
def algebraicTensorOperator :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →ₗ[ℂ]
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
  exact TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun T => (compactElementaryOperator H A a T :
            AdjointableOperator.End A (Space H A))
          map_add' := fun T U => by
            simp only [compactElementaryOperator_coe, map_add, mul_add]
          map_smul' := fun c T => by
            simp only [compactElementaryOperator_coe, map_smul]
            exact mul_smul_comm c (coefficientHom H A a) (compactHilbertHom H A T) }
      map_add' := fun a b => by
        apply LinearMap.ext
        intro T
        change (compactElementaryOperator H A (a + b) T : AdjointableOperator.End A (Space H A)) =
          (compactElementaryOperator H A a T : AdjointableOperator.End A (Space H A)) +
            (compactElementaryOperator H A b T : AdjointableOperator.End A (Space H A))
        simp only [compactElementaryOperator_coe, map_add, add_mul]
      map_smul' := fun c a => by
        apply LinearMap.ext
        intro T
        change (compactElementaryOperator H A (c • a) T : AdjointableOperator.End A (Space H A)) =
          c • (compactElementaryOperator H A a T : AdjointableOperator.End A (Space H A))
        simp only [compactElementaryOperator_coe, map_smul, smul_mul_assoc] }

/-- The neutral universal lift retains the exact original compact elementary tensor value. -/
theorem algebraicTensorOperator_tmul (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    algebraicTensorOperator H A (a ⊗ₜ[ℂ] T) =
      (compactElementaryOperator H A a T : AdjointableOperator.End A (Space H A)) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  rfl

/-- Actual factor commutation gives the original algebraic tensor multiplication law. -/
theorem algebraicTensorOperator_mul
    (z w : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    algebraicTensorOperator H A (z * w) =
      algebraicTensorOperator H A z * algebraicTensorOperator H A w := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  induction z using TensorProduct.inductionOn with
  | tmul a T =>
    induction w using TensorProduct.inductionOn with
    | tmul b U =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, algebraicTensorOperator_tmul,
        algebraicTensorOperator_tmul, algebraicTensorOperator_tmul]
      simp only [compactElementaryOperator_coe, map_mul]
      have hSwap : coefficientHom H A b * compactHilbertHom H A T =
          compactHilbertHom H A T * coefficientHom H A b :=
        (compactHilbertHom_commutes_coefficientHom H A T b).eq.symm
      calc
        (coefficientHom H A a * coefficientHom H A b) *
            (compactHilbertHom H A T * compactHilbertHom H A U) =
          coefficientHom H A a * (coefficientHom H A b * compactHilbertHom H A T) *
            compactHilbertHom H A U := by simp only [mul_assoc]
        _ = coefficientHom H A a * (compactHilbertHom H A T * coefficientHom H A b) *
            compactHilbertHom H A U := by rw [hSwap]
        _ = (coefficientHom H A a * compactHilbertHom H A T) *
            (coefficientHom H A b * compactHilbertHom H A U) := by simp only [mul_assoc]
    | add w w' hw hw' => simp only [mul_add, map_add, hw, hw']
  | add z z' hz hz' => simp only [add_mul, map_add, hz, hz']

/-- The genuine factor adjoints preserve the original algebraic tensor involution. -/
theorem algebraicTensorOperator_star
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    algebraicTensorOperator H A (star z) = star (algebraicTensorOperator H A z) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  induction z using TensorProduct.inductionOn with
  | tmul a T =>
    rw [TensorProduct.star_tmul, algebraicTensorOperator_tmul, algebraicTensorOperator_tmul]
    simp only [compactElementaryOperator_coe, star_mul]
    simpa only [map_star] using
      (compactHilbertHom_commutes_coefficientHom H A (star T) (star a)).eq.symm
  | add z w hz hw => simp only [star_add, map_add, hz, hw]

/-- Every original algebraic tensor has actual compact module image. -/
theorem algebraicTensorOperator_mem_compact
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    algebraicTensorOperator H A z ∈
      AdjointableOperator.compactSubmodule (B := A) (E := Space H A) (F := Space H A) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  induction z using TensorProduct.inductionOn with
  | tmul a T =>
    rw [algebraicTensorOperator_tmul]
    exact (compactElementaryOperator H A a T).property
  | add z w hz hw =>
    rw [map_add]
    exact Submodule.add_mem _ hz hw

/-- The actual algebraic A tensor K(full H) nonunital star homomorphism into its compact module target. -/
def algebraicCompactTensorHom :
    A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →⋆ₙₐ[ℂ] CompactAlgebra H A := by
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
  exact NonUnitalStarAlgHom.codRestrict
    (NonUnitalStarAlgHom.ofLinearMap (algebraicTensorOperator H A)
      (algebraicTensorOperator_mul H A) (algebraicTensorOperator_star H A))
    (AdjointableOperator.compactStarSubalgebra (B := A) (E := Space H A))
    (fun z => by
      change algebraicTensorOperator H A z ∈
        AdjointableOperator.compactSubmodule (B := A) (E := Space H A) (F := Space H A)
      exact algebraicTensorOperator_mem_compact H A z)

/-- The actual tensor star homomorphism retains each original compact elementary value. -/
theorem algebraicCompactTensorHom_tmul (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    algebraicCompactTensorHom H A (a ⊗ₜ[ℂ] T) = compactElementaryOperator H A a T := by
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
  apply Subtype.ext
  change algebraicTensorOperator H A (a ⊗ₜ[ℂ] T) =
    (compactElementaryOperator H A a T : AdjointableOperator.End A (Space H A))
  exact algebraicTensorOperator_tmul H A a T

/-- The actual algebraic tensor target acts by the original full-H elementary tensor formula. -/
theorem algebraicCompactTensorHom_pure (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) (ξ : H) (b : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    (algebraicCompactTensorHom H A (a ⊗ₜ[ℂ] T) : AdjointableOperator.End A (Space H A))
        (pure H A ξ b) = pure H A ((T : H →L[ℂ] H) ξ) (a * b) := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A
  let : NormedSpace ℂ (Space H A) := spaceNormedSpace H A
  let : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A
  let : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A
  rw [algebraicCompactTensorHom_tmul]
  change (coefficientHom H A a * compactHilbertHom H A T) (pure H A ξ b) =
    pure H A ((T : H →L[ℂ] H) ξ) (a * b)
  rw [AdjointableOperator.mul_apply, compactHilbertHom_pure, coefficientHom_pure]

end

end CStarModule.HilbertAmplification
