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
# Raw injectivity of the actual compact tensor action

Actual tensor matrix entries separate the compact-operator coefficients of
an internally chosen algebraic source basis. The stock tensor/Finsupp basis
equivalence is an original raw vector-space normal form; no faithful Hilbert
representation or tensor model is provided. Zero actual action forces every
matrix entry zero, every compact coefficient zero and thus the raw tensor zero.

This supplies actual raw definiteness needed by genuine cross-norm DATA for
the original minimum target. The least-cross-norm comparison and terminal
Takai/equivariance theorem proofs remain separate source obligations.
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

/-- Original coefficient basis coordinates commute with the actual Hilbert tensor matrix entries. -/
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

/-- Vanishing of every original tensor matrix entry forces the same raw algebraic tensor to be zero. -/
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

/-- The original algebraic compact-action operator is injective on its actual raw tensor carrier. -/
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

/-- The actual algebraic A tensor K(full H) compact-module star hom is genuinely raw-injective. -/
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

/-- The actually induced C-star seminorm is definite on the original raw compact tensor. -/
theorem compactTensorSeminorm_eq_zero_iff (z : A ⊗[ℂ] (compactEndomorphismClosedStarIdeal (H := H)).carrier) :
    compactTensorSeminorm H A z = 0 ↔ z = 0 := by
  let : NonUnitalCStarAlgebra (CompactAlgebra H A) := compactCStarAlgebra H A
  rw [compactTensorSeminorm_apply, norm_eq_zero]
  exact map_eq_zero_iff (algebraicCompactTensorHom H A) (injective_algebraicCompactTensorHom H A)

end

end CStarModule.HilbertAmplification
