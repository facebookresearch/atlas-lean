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
# Coefficient-valued matrix entries of compact tensors

For a complex Hilbert space `H` and nonunital C-star algebra `A`, the matrix-entry functional on
`K(H)` is `T ↦ ⟪η,T ξ⟫_ℂ`. Its complex-linear tensor lift satisfies `C_(ξ,η)(a⊗T) = ⟪η,T ξ⟫_ℂ •
a` in `A`.

For the algebraic tensor action `P_z` on `Space H A`, the coefficient pairing is `⟨η⊗c,
P_z(ξ⊗b)⟩_A = star c * (C_(ξ,η)(z) * b)`. Consequently a zero tensor action has every
coefficient entry zero, using C-star square definiteness, with no nonzero-space restriction.
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

/-- **Hilbert matrix-entry functional.** For `ξ,η : H`, this complex-linear functional on `K(H)`
sends `T` to `inner ℂ η (T ξ)`. -/
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

/-- **Value of a compact operator matrix entry.** `compactOperatorMatrixCoefficient H ξ η T =
inner ℂ η ((T : H →L[ℂ] H) ξ)`. -/
theorem compactOperatorMatrixCoefficient_apply (ξ η : H)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    compactOperatorMatrixCoefficient H ξ η T = inner ℂ η ((T : H →L[ℂ] H) ξ) := rfl

variable (A : Type uA) [NonUnitalCStarAlgebra A]

/-- **Coefficient-valued tensor matrix entry.** For nonunital `A` and `ξ,η : H`, the
complex-linear map `C_(ξ,η) : A ⊗_ℂ K(H) → A` is determined by `a⊗T ↦ ⟪η,T ξ⟫_ℂ • a`. -/
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

/-- **Matrix coefficient of a pure tensor.** `tensorMatrixCoefficient H A ξ η (a⊗T) =
compactOperatorMatrixCoefficient H ξ η T • a`. -/
theorem tensorMatrixCoefficient_tmul (ξ η : H) (a : A)
    (T : (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    tensorMatrixCoefficient H A ξ η (a ⊗ₜ[ℂ] T) = compactOperatorMatrixCoefficient H ξ η T • a := rfl

/-- **Pairing that recovers tensor coefficients.** For `z ∈ A ⊗_ℂ K(H)`, `ξ,η : H` and `c,b : A`,
`⟨pure η c, algebraicTensorOperator z (pure ξ b)⟩_A = star c * (tensorMatrixCoefficient ξ η z
* b)`. -/
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

/-- **Matrix entries of a zero tensor action.** If `algebraicTensorOperator H A z = 0`, then
`tensorMatrixCoefficient H A ξ η z = 0` for every `ξ,η : H`. -/
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
