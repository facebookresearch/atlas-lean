/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Norton transport of integral tensor vectors, using a single spin Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegralPowers

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

/-- A genuine pure Griess tensor from integer spin coordinates and the actual Leech basis. -/
noncomputable def monsterNortonIntegralTensorVector (v : NortonUIntegerVector) (z : Fin 24 → ℤ) :
    GriessSpace := griessConwayDecode (0, (0, conwayTensorCoordinates
      (nortonUIntegerEmbed v ⊗ₜ[ℝ] leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))))

/-- The defining vector has exactly its advertised pure tensor coordinates. -/
theorem monsterNortonIntegralTensorVector_encode (v : NortonUIntegerVector) (z : Fin 24 → ℤ) :
    griessConwayEncode (monsterNortonIntegralTensorVector v z) =
      (0, (0, conwayTensorCoordinates
        (nortonUIntegerEmbed v ⊗ₜ[ℝ] leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)))) :=
  griessConwayEncode_decode _ (by intro i j; rfl)

private theorem generated_tensor_coordinates (f : localFiberSubgroup) (x : GriessSpace) :
    (griessConwayEncode ((localIntoGenerated (QuotientGroup.mk f)).val x)).2.2 =
      localTensorRepresentation f (griessConwayEncode x).2.2 := by
  change (griessConwayEncode (localGriessRepresentation f x)).2.2 = _
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_tensor]

private theorem generated_tensor_product (f : localFiberSubgroup) (a : SpinSpace)
    (b : Fin 24 → ℝ) :
    (griessConwayEncode ((localIntoGenerated (QuotientGroup.mk f)).val
      (griessConwayDecode (0, (0, conwayTensorCoordinates (a ⊗ₜ[ℝ] b)))))).2.2 =
      conwayTensorCoordinates (f.val.1.val a ⊗ₜ[ℝ] f.val.2.val b) := by
  rw [generated_tensor_coordinates,
    griessConwayEncode_decode _ (by intro i j; rfl), localTensorRepresentation_coordinates]
  change conwayTensorCoordinates (TensorProduct.congr f.val.1.val f.val.2.val
    (a ⊗ₜ[ℝ] b)) = _
  rw [TensorProduct.congr_tmul]

/-- The actual Norton word transports every integral pure tensor by the exact compact numerator. -/
theorem monsterNortonUCompactTensor_forward (v : NortonUIntegerVector) (z : Fin 24 → ℤ)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (y555NortonActualU.val (monsterNortonIntegralTensorVector v z))).2.2 t i =
      (-1 / 8 : ℝ) * (monsterNortonUCompactNumerator v (nortonUIntegerLabel t) : ℝ) *
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ (monsterNortonUIntegralAction *ᵥ z)) i := by
  have h := generated_tensor_product monsterNortonUFiber (nortonUIntegerEmbed v)
    (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))
  change (griessConwayEncode ((localIntoGenerated monsterNortonULocal).val
    (monsterNortonIntegralTensorVector v z))).2.2 = _ at h
  rw [monsterNortonULocal_generated, monsterNortonUCompactSpin_actual_embed,
    monsterNortonUIntegralAction_basis] at h
  have ht := congrFun (congrFun h t) i
  simpa only [conwayTensorCoordinates_tmul, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerEmbed] using ht

/-- The actual inverse word has the analogous exact inverse spin and Leech tensor transport. -/
theorem monsterNortonUCompactTensor_inverse (v : NortonUIntegerVector) (z : Fin 24 → ℤ)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode ((y555NortonActualU⁻¹).val
      (monsterNortonIntegralTensorVector v z))).2.2 t i =
      (-1 / 8 : ℝ) * (monsterNortonUCompactInverseNumerator v (nortonUIntegerLabel t) : ℝ) *
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ
          (monsterNortonUInverseIntegralAction *ᵥ z)) i := by
  have h := generated_tensor_product monsterNortonUFiber⁻¹ (nortonUIntegerEmbed v)
    (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))
  change (griessConwayEncode ((localIntoGenerated (monsterNortonULocal⁻¹)).val
    (monsterNortonIntegralTensorVector v z))).2.2 =
      conwayTensorCoordinates ((monsterNortonUFiber.val.1⁻¹).val (nortonUIntegerEmbed v) ⊗ₜ[ℝ]
        (monsterNortonUFiber.val.2⁻¹).val
          (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))) at h
  have hLeech : (monsterNortonUFiber.val.2⁻¹).val
      (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
        leechCoordinateEmbedding
          (leechBasisMatrix *ᵥ (monsterNortonUInverseIntegralAction *ᵥ z)) :=
    monsterNortonUInverseIntegralAction_basis z
  rw [map_inv, monsterNortonULocal_generated, monsterNortonUCompactInverseSpin_actual_embed,
    hLeech] at h
  have ht := congrFun (congrFun h t) i
  simpa only [conwayTensorCoordinates_tmul, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerEmbed] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
