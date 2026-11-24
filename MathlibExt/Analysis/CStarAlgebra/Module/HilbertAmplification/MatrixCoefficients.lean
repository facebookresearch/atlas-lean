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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.AlgebraicTensorHom

/-!
# Actual coefficient-valued tensor matrix entries

Original Hilbert matrix entries are linear functionals on the full-H compact
ideal. Their neutral tensor lifts give actual A-valued entries of the original
algebraic compact action. The actual pure inner formula recovers those entries
from its original module action. A zero action has every entry zero by genuine
C-star square definiteness on the original coefficient algebra.

These are prerequisites of raw algebraic tensor injectivity, needed to build
definite cross-norm/minimum output data. No faithful representation, tensor
model, norm/equivalence certificate or nonzero-H assumption is provided.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions TensorProduct
open CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA

variable (H : Type uH)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The original full-H compact operator matrix entry as an actual complex linear functional. -/
def compactOperatorMatrixCoefficient (ξ η : H) :
    (compactEndomorphismClosedStarIdeal (H := H)).carrier →ₗ[ℂ] ℂ where
  toFun := fun T => inner ℂ η ((T : H →L[ℂ] H) ξ)
  map_add' := fun T U => by
    change inner ℂ η ((T : H →L[ℂ] H) ξ + (U : H →L[ℂ] H) ξ) =
      inner ℂ η ((T : H →L[ℂ] H) ξ) + inner ℂ η ((U : H →L[ℂ] H) ξ)
    exact _root_.inner_add_right _ _ _
  map_smul' := fun c T => by
    change inner ℂ η (c • ((T : H →L[ℂ] H) ξ)) = c * inner ℂ η ((T : H →L[ℂ] H) ξ)
    exact _root_.inner_smul_right _ _ _

/-- The linear functional has the literal original matrix entry on every compact operator. -/
theorem compactOperatorMatrixCoefficient_apply (ξ η : H)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    compactOperatorMatrixCoefficient H ξ η T = inner ℂ η ((T : H →L[ℂ] H) ξ) := rfl

variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- The neutral algebraic tensor lift of the original coefficient-valued matrix entries. -/
def tensorMatrixCoefficient (ξ η : H) : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier →ₗ[ℂ] A :=
  TensorProduct.lift
    { toFun := fun a => (compactOperatorMatrixCoefficient H ξ η).smulRight a
      map_add' := fun a b => by
        apply LinearMap.ext
        intro T
        change compactOperatorMatrixCoefficient H ξ η T • (a + b) =
          compactOperatorMatrixCoefficient H ξ η T • a + compactOperatorMatrixCoefficient H ξ η T • b
        exact smul_add _ _ _
      map_smul' := fun c a => by
        apply LinearMap.ext
        intro T
        change compactOperatorMatrixCoefficient H ξ η T • (c • a) =
          c • (compactOperatorMatrixCoefficient H ξ η T • a)
        exact smul_comm _ _ _ }

/-- Each original tensor matrix entry has its actual elementary scalar-times-coefficient value. -/
theorem tensorMatrixCoefficient_tmul (ξ η : H) (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    tensorMatrixCoefficient H A ξ η (a ⊗ₜ[ℂ] T) = compactOperatorMatrixCoefficient H ξ η T • a := rfl

/-- The original module inner action recovers every actual coefficient-valued tensor matrix entry. -/
theorem rightInner_algebraicTensorOperator_pure (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier)
    (ξ η : H) (c b : A) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    rightInner (B := A) (pure H A η c) (algebraicTensorOperator H A z (pure H A ξ b)) =
      star c * (tensorMatrixCoefficient H A ξ η z * b) := by
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
  induction z using TensorProduct.inductionOn with
  | tmul a T =>
    have hact : algebraicTensorOperator H A (a ⊗ₜ[ℂ] T) (pure H A ξ b) =
        pure H A ((T : H →L[ℂ] H) ξ) (a * b) :=
      algebraicCompactTensorHom_pure H A a T ξ b
    rw [hact, rightInner_pure, tensorMatrixCoefficient_tmul, compactOperatorMatrixCoefficient_apply]
    simp only [smul_mul_assoc, mul_smul_comm]
  | add z w hz hw =>
    rw [map_add]
    change rightInner (B := A) (pure H A η c)
      (algebraicTensorOperator H A z (pure H A ξ b) +
        algebraicTensorOperator H A w (pure H A ξ b)) =
          star c * (tensorMatrixCoefficient H A ξ η (z + w) * b)
    rw [CStarModule.rightInner_add_right, hz, hw, map_add, add_mul, mul_add]

/-- A zero original algebraic operator action forces every actual tensor matrix entry to vanish. -/
theorem tensorMatrixCoefficient_eq_zero_of_algebraicTensorOperator_eq_zero
    (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) (ξ η : H) :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    algebraicTensorOperator H A z = 0 → tensorMatrixCoefficient H A ξ η z = 0 := by
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
  intro hz
  let a : A := tensorMatrixCoefficient H A ξ η z
  have hab (b : A) : a * b = 0 := by
    have h := rightInner_algebraicTensorOperator_pure H A z ξ η (a * b) b
    rw [hz] at h
    change rightInner (B := A) (pure H A η (a * b)) (0 : Space H A) =
      star (a * b) * (a * b) at h
    rw [CStarModule.rightInner_zero_right] at h
    exact star_mul_self_eq_zero.mp h.symm
  exact mul_star_self_eq_zero.mp (hab (star a))

end

end CStarModule.HilbertAmplification
