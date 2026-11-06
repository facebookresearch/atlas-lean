/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole actual Griess-vector transport for the compact integer Norton tensor action. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSparseTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct Matrix
set_option backward.isDefEq.respectTransparency false

/-- A full actual local operator transports pure tensors by its spin and Leech factors. -/
theorem monsterNortonLocal_tensor_product_actual (f : localFiberSubgroup) (a : SpinSpace)
    (b : Fin 24 → ℝ) :
    localGriessRepresentation f
      (monsterNortonTensorLift (conwayTensorCoordinates (a ⊗ₜ[ℝ] b))) =
      monsterNortonTensorLift (conwayTensorCoordinates (f.val.1.val a ⊗ₜ[ℝ] f.val.2.val b)) := by
  apply (Function.LeftInverse.injective griessConwayDecode_encode)
  rw [monsterNortonTensorLift_apply, localGriessRepresentation_encode,
    griessConwayEncode_decode _ (by intros; rfl), monsterNortonTensorLift_apply,
    griessConwayEncode_decode _ (by intros; rfl), localConwayRawRepresentation_apply]
  simp only [map_zero]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  rw [localTensorRepresentation_coordinates]
  change conwayTensorCoordinates (TensorProduct.congr f.val.1.val f.val.2.val
    (a ⊗ₜ[ℝ] b)) = _
  rw [TensorProduct.congr_tmul]

/-- The complete actual Norton word has this whole-vector integer tensor transport. -/
theorem monsterNortonUCompactIntegralVector_forward (v : NortonUIntegerVector)
    (z : Fin 24 → ℤ) :
    y555NortonActualU.val (monsterNortonIntegralTensorVector v z) =
      (-1 / 8 : ℝ) • monsterNortonIntegralTensorVector
        (monsterNortonUCompactNumerator v) (monsterNortonUIntegralAction *ᵥ z) := by
  rw [← monsterNortonULocal_generated]
  change localGriessRepresentation monsterNortonUFiber
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed v ⊗ₜ[ℝ] leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))) = _
  rw [monsterNortonLocal_tensor_product_actual, monsterNortonUCompactSpin_actual_embed,
    monsterNortonUIntegralAction_basis]
  change monsterNortonTensorLift (conwayTensorCoordinates
    (((-1 / 8 : ℝ) • nortonUIntegerEmbed (monsterNortonUCompactNumerator v)) ⊗ₜ[ℝ]
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (monsterNortonUIntegralAction *ᵥ z)))) =
    (-1 / 8 : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed (monsterNortonUCompactNumerator v) ⊗ₜ[ℝ]
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (monsterNortonUIntegralAction *ᵥ z))))
  rw [← TensorProduct.smul_tmul', map_smul, map_smul]

/-- The genuine inverse Norton word has the corresponding whole-vector integer transport. -/
theorem monsterNortonUCompactIntegralVector_inverse (v : NortonUIntegerVector)
    (z : Fin 24 → ℤ) :
    (y555NortonActualU⁻¹).val (monsterNortonIntegralTensorVector v z) =
      (-1 / 8 : ℝ) • monsterNortonIntegralTensorVector
        (monsterNortonUCompactInverseNumerator v) (monsterNortonUInverseIntegralAction *ᵥ z) := by
  rw [← monsterNortonULocal_generated, ← map_inv]
  change localGriessRepresentation (monsterNortonUFiber⁻¹)
    (monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed v ⊗ₜ[ℝ] leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))) = _
  rw [monsterNortonLocal_tensor_product_actual]
  change monsterNortonTensorLift (conwayTensorCoordinates
    ((monsterNortonUFiber.val.1⁻¹).val (nortonUIntegerEmbed v) ⊗ₜ[ℝ]
      (monsterNortonUFiber.val.2⁻¹).val
        (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))) = _
  rw [monsterNortonUCompactInverseSpin_actual_embed]
  have hz : (monsterNortonUFiber.val.2⁻¹).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ
          (monsterNortonUInverseIntegralAction *ᵥ z)) :=
    monsterNortonUInverseIntegralAction_basis z
  rw [hz]
  change monsterNortonTensorLift (conwayTensorCoordinates
    (((-1 / 8 : ℝ) • nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator v)) ⊗ₜ[ℝ]
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ
        (monsterNortonUInverseIntegralAction *ᵥ z)))) =
    (-1 / 8 : ℝ) • monsterNortonTensorLift (conwayTensorCoordinates
      (nortonUIntegerEmbed (monsterNortonUCompactInverseNumerator v) ⊗ₜ[ℝ]
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (monsterNortonUInverseIntegralAction *ᵥ z))))
  rw [← TensorProduct.smul_tmul', map_smul, map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
