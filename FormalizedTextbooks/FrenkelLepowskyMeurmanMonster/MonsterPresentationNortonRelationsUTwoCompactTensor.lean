/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Norton transport of integral tensor vectors, using a single spin Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoCompactSpinInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix TensorProduct
set_option backward.isDefEq.respectTransparency false

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

private theorem fiber_square_spin (f : localFiberSubgroup) :
    (f ^ 2).val.1 = f.val.1 ^ 2 := rfl

private theorem fiber_inverse_spin (f : localFiberSubgroup) :
    (f⁻¹).val.1 = f.val.1⁻¹ := rfl

set_option maxRecDepth 10000 in
/-- The actual Norton word transports every integral pure tensor by the exact compact numerator. -/
theorem monsterNortonUTwoCompactTensor_forward (v : NortonUIntegerVector) (z : Fin 24 → ℤ)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode ((y555NortonActualU ^ 2).val (monsterNortonIntegralTensorVector v
      z))).2.2 t i =
      (1 / 4 : ℝ) * (monsterNortonUTwoCompactNumerator v (nortonUIntegerLabel t) : ℝ) *
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ ((monsterNortonUIntegralAction ^ 2) *ᵥ
          z)) i := by
  have h := generated_tensor_product (monsterNortonUFiber ^ 2) (nortonUIntegerEmbed v)
    (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))
  change (griessConwayEncode ((localIntoGenerated
    (QuotientGroup.mk' localDiagonalSubgroup (monsterNortonUFiber ^ 2))).val
    (monsterNortonIntegralTensorVector v z))).2.2 = _ at h
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      (monsterNortonUFiber ^ 2)) = y555NortonActualU ^ 2 := by
    simpa only [zpow_ofNat] using monsterNortonUFiber_generated_zpow (2 : ℤ)
  rw [hg] at h
  rw [fiber_square_spin] at h
  rw [monsterNortonUTwoCompactSpin_actual_embed,
    monsterNortonUIntegralAction_power_basis] at h
  have ht := congrFun (congrFun h t) i
  simpa only [conwayTensorCoordinates_tmul, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerEmbed] using ht

set_option maxRecDepth 10000 in
/-- The actual inverse word has the analogous exact inverse spin and Leech tensor transport. -/
theorem monsterNortonUTwoCompactTensor_inverse (v : NortonUIntegerVector) (z : Fin 24 → ℤ)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (((y555NortonActualU ^ 2)⁻¹).val
      (monsterNortonIntegralTensorVector v z))).2.2 t i =
      (1 / 4 : ℝ) * (monsterNortonUTwoCompactInverseNumerator v (nortonUIntegerLabel t) : ℝ) *
        leechCoordinateEmbedding (leechBasisMatrix *ᵥ
          ((monsterNortonUInverseIntegralAction ^ 2) *ᵥ z)) i := by
  have h := generated_tensor_product ((monsterNortonUFiber⁻¹) ^ 2)
    (nortonUIntegerEmbed v) (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z))
  change (griessConwayEncode ((localIntoGenerated
    (QuotientGroup.mk' localDiagonalSubgroup ((monsterNortonUFiber⁻¹) ^ 2))).val
    (monsterNortonIntegralTensorVector v z))).2.2 = _ at h
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      ((monsterNortonUFiber⁻¹) ^ 2)) = (y555NortonActualU ^ 2)⁻¹ := by
    simpa only [zpow_neg, zpow_ofNat, inv_pow] using
      monsterNortonUFiber_generated_zpow (-2 : ℤ)
  rw [hg] at h
  have hs : ((monsterNortonUFiber⁻¹) ^ 2).val.1.val (nortonUIntegerEmbed v) =
      (1 / 4 : ℝ) • nortonUIntegerEmbed (monsterNortonUTwoCompactInverseNumerator v) := by
    rw [fiber_square_spin, fiber_inverse_spin, inv_pow]
    exact monsterNortonUTwoCompactInverseSpin_actual_embed v
  rw [hs, monsterNortonUInverseIntegralAction_power_basis] at h
  have ht := congrFun (congrFun h t) i
  simpa only [conwayTensorCoordinates_tmul, Pi.smul_apply, smul_eq_mul,
    nortonUIntegerEmbed] using ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
