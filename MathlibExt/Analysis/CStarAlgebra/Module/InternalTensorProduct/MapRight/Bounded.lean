/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.MapRight
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.PreHilbert
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.CommutingSquareComplement

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Bounded commuting second-factor maps on the original radical tensor

The positive CFC square complement stays in the represented commutant. Its
actual second-factor tensor map gives a positive remainder in the original
coefficient-valued inner form. The resulting bound uses the actual quotient
norm; no tensor norm, null witness or completed model is supplied.

This bound is the prerequisite for the original coefficient action on the
Hilbert amplification in Blackadar, K-Theory for Operator Algebras, 10.1.2.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁]
  [PartialOrder B₁ᵐᵒᵖ] [StarOrderedRing B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂]
  [PartialOrder B₂ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁] [CompleteSpace E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂] [CompleteSpace E₂]

omit [StarOrderedRing B₁ᵐᵒᵖ] [StarOrderedRing B₂ᵐᵒᵖ]
  [CompleteSpace E₁] [CompleteSpace E₂] in
private theorem rawRightFactorMap_squareSplit
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S Q : AdjointableOperator.End B₂ E₂)
    (hS : ∀ b : B₁, Commute S (φ b)) (hQ : ∀ b : B₁, Commute Q (φ b))
    (hSquare : ∀ y : E₂, S.adjoint (S y) + Q.adjoint (Q y) = (‖S‖ ^ 2 : ℝ) • y)
    (z w : AlgebraicTensor E₁ E₂) :
    rawInner φ (rawRightFactorMap S z) (rawRightFactorMap S w) +
        rawInner φ (rawRightFactorMap Q z) (rawRightFactorMap Q w) =
      (‖S‖ ^ 2 : ℝ) • rawInner φ z w := by
  have hMoveS (b : B₁) (v : E₂) :
      S.adjoint (φ b (S v)) = φ b (S.adjoint (S v)) := by
    simpa only [AdjointableOperator.mul_apply, AdjointableOperator.adjointOperator_apply] using
      congrArg (fun T : AdjointableOperator.End B₂ E₂ => T (S v))
        (rightFactorCommutant_adjoint φ S hS b).eq
  have hMoveQ (b : B₁) (v : E₂) :
      Q.adjoint (φ b (Q v)) = φ b (Q.adjoint (Q v)) := by
    simpa only [AdjointableOperator.mul_apply, AdjointableOperator.adjointOperator_apply] using
      congrArg (fun T : AdjointableOperator.End B₂ E₂ => T (Q v))
        (rightFactorCommutant_adjoint φ Q hQ b).eq
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      simp only [rawRightFactorMap_tmul, rawInner_tmul_tmul]
      rw [S.adjoint_inner, Q.adjoint_inner, hMoveS, hMoveQ,
        ← rightInner_add_right, ← map_add, hSquare]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (‖S‖ ^ 2) v,
        map_smul, rightInner_smul_right]
      exact (RCLike.real_smul_eq_coe_smul (K := ℂ) (‖S‖ ^ 2)
        (rightInner (B := B₂) u (φ (rightInner (B := B₁) x y) v))).symm
    | add w w' hw hw' =>
      simp only [map_add, smul_add]
      rw [add_add_add_comm, hw, hw']
  | add z z' hz hz' =>
    simp only [map_add, LinearMap.add_apply, smul_add]
    rw [add_add_add_comm, hz, hz']

/-- The actual second-factor map is bounded in the original quotient norm. -/
theorem radicalRightFactorMap_norm_le
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (q : RadicalTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    ‖radicalRightFactorMap φ S hComm q‖ ≤ ‖S‖ * ‖q‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  obtain ⟨Q, hQComm, hSquare⟩ :=
    AdjointableOperator.exists_commuting_norm_square_complement φ S hComm
  have hSplit :
      radicalInner φ (radicalRightFactorMap φ S hComm q) (radicalRightFactorMap φ S hComm q) +
        radicalInner φ (radicalRightFactorMap φ Q hQComm q) (radicalRightFactorMap φ Q hQComm q) =
      (‖S‖ ^ 2 : ℝ) • radicalInner φ q q := by
    obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective q
    obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective w
    simpa only [radicalRightFactorMap_mkQ, balancedRightFactorMap_mkQ,
      radicalInner_mkQ_mkQ, balancedInner_mkQ_mkQ] using
        rawRightFactorMap_squareSplit φ S Q hComm hQComm hSquare z z
  have hPosS : 0 ≤ MulOpposite.op
      (radicalInner φ (radicalRightFactorMap φ S hComm q) (radicalRightFactorMap φ S hComm q)) := by
    obtain ⟨w, hw⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective
      (radicalRightFactorMap φ S hComm q)
    rw [← hw, radicalInner_mkQ_mkQ]
    exact balancedInner_self_nonneg φ w
  have hPosQ : 0 ≤ MulOpposite.op
      (radicalInner φ (radicalRightFactorMap φ Q hQComm q) (radicalRightFactorMap φ Q hQComm q)) := by
    obtain ⟨w, hw⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective
      (radicalRightFactorMap φ Q hQComm q)
    rw [← hw, radicalInner_mkQ_mkQ]
    exact balancedInner_self_nonneg φ w
  have hOp :
      MulOpposite.op
          (radicalInner φ (radicalRightFactorMap φ S hComm q) (radicalRightFactorMap φ S hComm q)) +
        MulOpposite.op
          (radicalInner φ (radicalRightFactorMap φ Q hQComm q) (radicalRightFactorMap φ Q hQComm q)) =
      (‖S‖ ^ 2 : ℝ) • MulOpposite.op (radicalInner φ q q) := by
    simpa only [MulOpposite.op_add, MulOpposite.op_smul] using congrArg MulOpposite.op hSplit
  have hle :
      MulOpposite.op
          (radicalInner φ (radicalRightFactorMap φ S hComm q) (radicalRightFactorMap φ S hComm q)) ≤
        (‖S‖ ^ 2 : ℝ) • MulOpposite.op (radicalInner φ q q) :=
    (le_add_of_nonneg_right hPosQ).trans_eq hOp
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hPosS
  have hsq : ‖radicalRightFactorMap φ S hComm q‖ ^ 2 ≤ (‖S‖ * ‖q‖) ^ 2 := by
    calc
      ‖radicalRightFactorMap φ S hComm q‖ ^ 2 =
          ‖MulOpposite.op
            (radicalInner φ (radicalRightFactorMap φ S hComm q)
              (radicalRightFactorMap φ S hComm q))‖ := by
        rw [radicalTensorNormedAddCommGroup_norm,
          Real.sq_sqrt (_root_.norm_nonneg _), MulOpposite.norm_op]
      _ ≤ ‖(‖S‖ ^ 2 : ℝ) • MulOpposite.op (radicalInner φ q q)‖ := hn
      _ = (‖S‖ * ‖q‖) ^ 2 := by
        rw [_root_.norm_smul, Real.norm_of_nonneg (sq_nonneg ‖S‖), MulOpposite.norm_op]
        rw [radicalTensorNormedAddCommGroup_norm, mul_pow,
          Real.sq_sqrt (_root_.norm_nonneg _)]
  exact (sq_le_sq₀ (_root_.norm_nonneg (radicalRightFactorMap φ S hComm q))
    (mul_nonneg (_root_.norm_nonneg S) (_root_.norm_nonneg q))).mp hsq

/-- The actual radical map with continuity from its proved source bound. -/
def radicalRightFactorCLM
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    RadicalTensor (E₁ := E₁) φ →L[ℂ] RadicalTensor (E₁ := E₁) φ := by
  letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
    radicalTensorNormedAddCommGroup φ
  letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  exact (radicalRightFactorMap φ S hComm).mkContinuous ‖S‖
    (fun q => radicalRightFactorMap_norm_le φ S hComm q)

/-- Continuity retains every original algebraic quotient value. -/
@[simp]
theorem radicalRightFactorCLM_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (q : RadicalTensor (E₁ := E₁) φ) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    radicalRightFactorCLM φ S hComm q = radicalRightFactorMap φ S hComm q := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  rfl

/-- The actual radical CLM retains its source operator-norm estimate. -/
theorem radicalRightFactorCLM_norm_le
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    letI : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) :=
      radicalTensorNormedAddCommGroup φ;
    letI : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ;
    ‖radicalRightFactorCLM (E₁ := E₁) φ S hComm‖ ≤ ‖S‖ := by
  let : NormedAddCommGroup (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedAddCommGroup φ
  let : NormedSpace ℂ (RadicalTensor (E₁ := E₁) φ) := radicalTensorNormedSpace φ
  let F : RadicalTensor (E₁ := E₁) φ →L[ℂ] RadicalTensor (E₁ := E₁) φ :=
    radicalRightFactorCLM φ S hComm
  change ‖F‖ ≤ ‖S‖
  refine ContinuousLinearMap.opNorm_le_bound F (_root_.norm_nonneg S) ?_
  intro q
  change ‖radicalRightFactorCLM φ S hComm q‖ ≤ ‖S‖ * ‖q‖
  rw [radicalRightFactorCLM_apply]
  exact radicalRightFactorMap_norm_le φ S hComm q

end CStarModule.InternalTensorProduct
