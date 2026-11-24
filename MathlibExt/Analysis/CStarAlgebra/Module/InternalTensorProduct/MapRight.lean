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

public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.Radical

/-!
# Commuting second-factor maps on actual internal tensors

An adjointable map on the second factor that commutes with the given coefficient
representation induces maps on the original complex, balanced and radical
tensor carriers. Its genuine adjoint supplies the paired radical map.

This is the algebraic prerequisite for the coefficient action on the original
Hilbert amplification in Blackadar, K-Theory for Operator Algebras, 10.1.2.
The second-factor norm bound and completed operator are separate constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped TensorProduct RightActions

namespace CStarModule.InternalTensorProduct

universe uB₁ uB₂ uE₁ uE₂

variable {B₁ : Type uB₁} [NonUnitalCStarAlgebra B₁] [PartialOrder B₁ᵐᵒᵖ]
variable {B₂ : Type uB₂} [NonUnitalCStarAlgebra B₂] [PartialOrder B₂ᵐᵒᵖ]
variable {E₁ : Type uE₁} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [SMul B₁ᵐᵒᵖ E₁] [CStarModule B₁ᵐᵒᵖ E₁]
variable {E₂ : Type uE₂} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  [SMul B₂ᵐᵒᵖ E₂] [CStarModule B₂ᵐᵒᵖ E₂]

/-- The original complex tensor map induced by the actual second-factor map. -/
def rawRightFactorMap (S : AdjointableOperator.End B₂ E₂) :
    AlgebraicTensor E₁ E₂ →ₗ[ℂ] AlgebraicTensor E₁ E₂ :=
  TensorProduct.map LinearMap.id S.toContinuousLinearMap.toLinearMap

/-- The actual raw map changes only the original second factor. -/
@[simp]
theorem rawRightFactorMap_tmul (S : AdjointableOperator.End B₂ E₂)
    (x : E₁) (y : E₂) :
    rawRightFactorMap S (x ⊗ₜ[ℂ] y) = x ⊗ₜ[ℂ] (S y) := by
  simp only [rawRightFactorMap, TensorProduct.map_tmul, LinearMap.id_apply,
    ContinuousLinearMap.coe_coe, AdjointableOperator.coe_toContinuousLinearMap]

omit [PartialOrder B₁ᵐᵒᵖ] in
/-- Commutation with a star representation also holds for the genuine adjoint. -/
theorem rightFactorCommutant_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    ∀ b : B₁, Commute S.adjointOperator (φ b) := by
  intro b
  change Commute (star S) (φ b)
  simpa only [map_star, star_star] using (hComm (star b)).star_star

omit [PartialOrder B₁ᵐᵒᵖ] in
private theorem rightFactorCommutant_apply
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (b : B₁) (y : E₂) :
    S (φ b y) = φ b (S y) := by
  simpa only [AdjointableOperator.mul_apply] using
    congrArg (fun T : AdjointableOperator.End B₂ E₂ => T y) (hComm b).eq

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- Coefficient commutation preserves the literal balancing span. -/
theorem balancingSpan_rawRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    balancingSpan (E₁ := E₁) φ ≤
      (balancingSpan (E₁ := E₁) φ).comap (rawRightFactorMap S) := by
  apply Submodule.span_le.2
  rintro _ ⟨⟨x, b, y⟩, rfl⟩
  change rawRightFactorMap S (balanceRelation φ x b y) ∈ balancingSpan (E₁ := E₁) φ
  simpa only [balanceRelation, map_sub, rawRightFactorMap_tmul,
    rightFactorCommutant_apply φ S hComm] using balanceRelation_mem φ x b (S y)

/-- The actual second-factor adjoint gives the original raw-inner identity. -/
theorem rawRightFactorMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b))
    (z w : AlgebraicTensor E₁ E₂) :
    rawInner φ (rawRightFactorMap S z) w =
      rawInner φ z (rawRightFactorMap S.adjointOperator w) := by
  induction z using TensorProduct.inductionOn with
  | tmul x u =>
    induction w using TensorProduct.inductionOn with
    | tmul y v =>
      simp only [rawRightFactorMap_tmul, rawInner_tmul_tmul,
        AdjointableOperator.adjoint_inner]
      rw [← AdjointableOperator.adjointOperator_apply,
        rightFactorCommutant_apply φ S.adjointOperator
          (rightFactorCommutant_adjoint φ S hComm)]
    | add w w' hw hw' => simp only [map_add, hw, hw']
  | add z z' hz hz' => simp only [map_add, LinearMap.add_apply, hz, hz']

/-- The second-factor map retains the original right coefficient action. -/
theorem rawRightFactorMap_rawRightSMul
    (S : AdjointableOperator.End B₂ E₂) (b : B₂)
    (z : AlgebraicTensor E₁ E₂) :
    rawRightFactorMap S (rawRightSMul b z) =
      rawRightSMul b (rawRightFactorMap S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [rawRightSMul_tmul, rawRightFactorMap_tmul,
      AdjointableOperator.map_right_smul]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The computed second-factor map on the genuine balanced quotient. -/
def balancedRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    BalancedTensor (E₁ := E₁) φ →ₗ[ℂ] BalancedTensor (E₁ := E₁) φ :=
  (balancingSpan (E₁ := E₁) φ).mapQ (balancingSpan (E₁ := E₁) φ)
    (rawRightFactorMap S) (balancingSpan_rawRightFactorMap φ S hComm)

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- Every original raw representative has its literal descended image. -/
theorem balancedRightFactorMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (z : AlgebraicTensor E₁ E₂) :
    balancedRightFactorMap φ S hComm ((balancingSpan (E₁ := E₁) φ).mkQ z) =
      (balancingSpan (E₁ := E₁) φ).mkQ (rawRightFactorMap S z) := by
  simp only [balancedRightFactorMap, Submodule.mkQ_apply, Submodule.mapQ_apply]

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- Balanced pure tensors retain the original second-factor formula. -/
@[simp]
theorem balancedRightFactorMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (x : E₁) (y : E₂) :
    balancedRightFactorMap φ S hComm (balancedPure φ x y) =
      balancedPure φ x (S y) := by
  simp only [balancedPure, balancedRightFactorMap_mkQ, rawRightFactorMap_tmul]

/-- Both balanced descents retain the actual paired-adjoint equation. -/
theorem balancedRightFactorMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b))
    (z w : BalancedTensor (E₁ := E₁) φ) :
    balancedInner φ (balancedRightFactorMap φ S hComm z) w =
      balancedInner φ z (balancedRightFactorMap φ S.adjointOperator
        (rightFactorCommutant_adjoint φ S hComm) w) := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective w
  simpa only [balancedRightFactorMap_mkQ, balancedInner_mkQ_mkQ] using
    rawRightFactorMap_inner_adjoint φ S hComm z w

omit [PartialOrder B₁ᵐᵒᵖ] [CStarModule B₁ᵐᵒᵖ E₁] in
/-- The original right coefficient action commutes with the balanced map. -/
theorem balancedRightFactorMap_balancedRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (b : B₂)
    (z : BalancedTensor (E₁ := E₁) φ) :
    balancedRightFactorMap φ S hComm (balancedRightSMul φ b z) =
      balancedRightSMul φ b (balancedRightFactorMap φ S hComm z) := by
  obtain ⟨z, rfl⟩ := (balancingSpan (E₁ := E₁) φ).mkQ_surjective z
  simpa only [balancedRightFactorMap_mkQ, balancedRightSMul_mkQ] using
    congrArg (balancingSpan (E₁ := E₁) φ).mkQ
      (rawRightFactorMap_rawRightSMul S b z)

/-- The proved actual adjoint identity preserves the original radical. -/
theorem radicalSpace_balancedRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    radicalSpace (E₁ := E₁) φ ≤
      (radicalSpace (E₁ := E₁) φ).comap (balancedRightFactorMap φ S hComm) := by
  intro z hz
  change balancedRightFactorMap φ S hComm z ∈ radicalSpace (E₁ := E₁) φ
  apply (mem_radicalSpace_iff φ _).mpr
  intro w
  rw [balancedRightFactorMap_inner_adjoint]
  exact (mem_radicalSpace_iff φ z).mp hz _

/-- The genuine second-factor map on the original radical quotient. -/
def radicalRightFactorMap
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) :
    RadicalTensor (E₁ := E₁) φ →ₗ[ℂ] RadicalTensor (E₁ := E₁) φ :=
  (radicalSpace (E₁ := E₁) φ).mapQ (radicalSpace (E₁ := E₁) φ)
    (balancedRightFactorMap φ S hComm) (radicalSpace_balancedRightFactorMap φ S hComm)

/-- Each original balanced representative has the computed radical image. -/
theorem radicalRightFactorMap_mkQ
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (z : BalancedTensor (E₁ := E₁) φ) :
    radicalRightFactorMap φ S hComm ((radicalSpace (E₁ := E₁) φ).mkQ z) =
      (radicalSpace (E₁ := E₁) φ).mkQ (balancedRightFactorMap φ S hComm z) := by
  simp only [radicalRightFactorMap, Submodule.mkQ_apply, Submodule.mapQ_apply]

/-- The original radical pure tensors have the printed second-factor value. -/
theorem radicalRightFactorMap_pure
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (x : E₁) (y : E₂) :
    radicalRightFactorMap φ S hComm ((radicalSpace (E₁ := E₁) φ).mkQ (balancedPure φ x y)) =
      (radicalSpace (E₁ := E₁) φ).mkQ (balancedPure φ x (S y)) := by
  simp only [radicalRightFactorMap_mkQ, balancedRightFactorMap_pure]

/-- Both radical descents retain the original paired-adjoint identity. -/
theorem radicalRightFactorMap_inner_adjoint
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b))
    (z w : RadicalTensor (E₁ := E₁) φ) :
    radicalInner φ (radicalRightFactorMap φ S hComm z) w =
      radicalInner φ z (radicalRightFactorMap φ S.adjointOperator
        (rightFactorCommutant_adjoint φ S hComm) w) := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  obtain ⟨w, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective w
  simpa only [radicalRightFactorMap_mkQ, radicalInner_mkQ_mkQ] using
    balancedRightFactorMap_inner_adjoint φ S hComm z w

/-- The original coefficient action commutes with the radical map. -/
theorem radicalRightFactorMap_radicalRightSMul
    (φ : B₁ →⋆ₙₐ[ℂ] AdjointableOperator.End B₂ E₂)
    (S : AdjointableOperator.End B₂ E₂)
    (hComm : ∀ b : B₁, Commute S (φ b)) (b : B₂)
    (z : RadicalTensor (E₁ := E₁) φ) :
    radicalRightFactorMap φ S hComm (radicalRightSMul φ b z) =
      radicalRightSMul φ b (radicalRightFactorMap φ S hComm z) := by
  obtain ⟨z, rfl⟩ := (radicalSpace (E₁ := E₁) φ).mkQ_surjective z
  simpa only [radicalRightFactorMap_mkQ, radicalRightSMul_mkQ] using
    congrArg (radicalSpace (E₁ := E₁) φ).mkQ
      (balancedRightFactorMap_balancedRightSMul φ S hComm b z)

end CStarModule.InternalTensorProduct
