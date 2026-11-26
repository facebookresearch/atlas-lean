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

public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.MatrixCoefficients
public import MathlibExt.Analysis.CStarAlgebra.Module.HilbertAmplification.InducedCompletion

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Injectivity of the algebraic compact tensor action

For complex Hilbert `H` and nonunital C-star `A`, the coefficient maps `C_(ξ,η) : A ⊗_ℂ K(H) →
A` separate algebraic tensors. A basis of the complex vector space `A` converts these entries
into the Hilbert matrix entries of the compact coefficients.

A zero operator action has zero matrix entries, so every compact coefficient and then the tensor
itself is zero. Therefore the algebraic compact tensor representation is injective, and its
induced C-star seminorm satisfies `p(z) = 0 ↔ z = 0`. No nonzero Hilbert-space hypothesis is
needed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra ComplexOrder RightActions TensorProduct
open CStarModule.InternalTensorProduct

namespace CStarModule.HilbertAmplification

noncomputable section

universe uH uA uI

variable (H : Type uH) (A : Type uA)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NonUnitalCStarAlgebra A]

/-- **Basis coordinates of tensor matrix entries.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, for a complex basis `B : Module.Basis I ℂ A`, `B.coord i
(tensorMatrixCoefficient ξ η z)` equals the compact matrix entry of the `i`-th coefficient in
the tensor-basis representation of `z`. -/
theorem tensorMatrixCoefficient_basisCoordinate {I : Type uI} (B : Module.Basis I ℂ A) (i : I)
    (ξ η : H) (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    letI : DecidableEq I := Classical.decEq I;
    B.coord i (tensorMatrixCoefficient H A ξ η z) =
      compactOperatorMatrixCoefficient H ξ η (TensorProduct.equivFinsuppOfBasisLeft B z i) := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul a T =>
    rw [tensorMatrixCoefficient_tmul,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul, map_smul]
    change compactOperatorMatrixCoefficient H ξ η T * B.repr a i =
      B.repr a i * compactOperatorMatrixCoefficient H ξ η T
    exact mul_comm _ _
  | add z w hz hw =>
    rw [map_add, map_add, map_add, Finsupp.add_apply, map_add, hz, hw]

/-- **Tensor determined by its Hilbert entries.** For a complex Hilbert space `H` and a nonunital
C-star algebra `A`, if `tensorMatrixCoefficient H A ξ η z = 0` for every `ξ,η : H`, then the
algebraic tensor `z` is zero. -/
theorem eq_zero_of_tensorMatrixCoefficient_eq_zero (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier)
    (hz : ∀ ξ η : H, tensorMatrixCoefficient H A ξ η z = 0) : z = 0 := by
  classical
  let B : Module.Basis (Module.Free.ChooseBasisIndex ℂ A) ℂ A := Module.Free.chooseBasis ℂ A
  let e : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier ≃ₗ[ℂ]
      Module.Free.ChooseBasisIndex ℂ A →₀ (compactEndomorphismClosedStarIdeal (H := H)).carrier :=
    TensorProduct.equivFinsuppOfBasisLeft B
  have hcoeff (i : Module.Free.ChooseBasisIndex ℂ A) : e z i = 0 := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro ξ
    apply (_root_.inner_self_eq_zero (𝕜 := ℂ)).mp
    have h := tensorMatrixCoefficient_basisCoordinate H A B i ξ ((e z i : H →L[ℂ] H) ξ) z
    rw [hz, map_zero] at h
    have hzero : compactOperatorMatrixCoefficient H ξ ((e z i : H →L[ℂ] H) ξ) (e z i) = 0 :=
      h.symm
    exact hzero
  have he : e z = 0 := Finsupp.ext fun i => hcoeff i
  have he0 : e (0 : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) = 0 :=
    map_zero e
  exact e.injective (he.trans he0.symm)

/-- **Injective algebraic operator representation.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, the map `algebraicTensorOperator H A : A ⊗_ℂ K(H) → End_A(Space
H A)` is injective. -/
theorem injective_algebraicTensorOperator :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : NormedAddCommGroup (Space H A) := spaceNormedAddCommGroup H A;
    letI : NormedSpace ℂ (Space H A) := spaceNormedSpace H A;
    letI : SMul Aᵐᵒᵖ (Space H A) := spaceOppositeSMul H A;
    letI : CStarModule Aᵐᵒᵖ (Space H A) := spaceCStarModule H A;
    Function.Injective (algebraicTensorOperator H A) := by
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
  intro z w hzw
  have hzero : algebraicTensorOperator H A (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  have hm : ∀ ξ η : H, tensorMatrixCoefficient H A ξ η (z - w) = 0 := fun ξ η =>
    tensorMatrixCoefficient_eq_zero_of_algebraicTensorOperator_eq_zero H A (z - w) ξ η hzero
  exact sub_eq_zero.mp (eq_zero_of_tensorMatrixCoefficient_eq_zero H A (z - w) hm)

/-- **Injective algebraic compact representation.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, `algebraicCompactTensorHom H A` is injective on `A ⊗_ℂ K(H)`. -/
theorem injective_algebraicCompactTensorHom : Function.Injective (algebraicCompactTensorHom H A) := by
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
  intro z w hzw
  apply injective_algebraicTensorOperator H A
  exact congrArg (fun T : CompactAlgebra H A =>
    (T : AdjointableOperator.End A (Space H A))) hzw

/-- **Definiteness of the induced compact tensor norm.** For a complex Hilbert space `H` and a
nonunital C-star algebra `A`, `compactTensorSeminorm H A z = 0` if and only if `z = 0`. -/
theorem compactTensorSeminorm_eq_zero_iff (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    compactTensorSeminorm H A z = 0 ↔ z = 0 := by
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  rw [compactTensorSeminorm_apply, norm_eq_zero]
  exact map_eq_zero_iff (algebraicCompactTensorHom H A) (injective_algebraicCompactTensorHom H A)

end

end CStarModule.HilbertAmplification
