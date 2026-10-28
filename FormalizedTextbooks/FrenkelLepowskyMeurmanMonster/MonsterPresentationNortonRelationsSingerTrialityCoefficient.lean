/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- One physical tensor row of the actual Singer-triality commutator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerShort
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerCoordinateIdentity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorInverseTrialityFullCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem zero_label : golayLabelCoefficients (0 : Fin 4096) = 0 := by
  decide +kernel

private theorem omega_label : golayLabelCoefficients (2048 : Fin 4096) =
    Pi.single (11 : Fin 12) (1 : ZMod 2) := by
  decide +kernel

private theorem singer_omega : monsterNortonSingerCode 0
    (Pi.single (11 : Fin 12) (1 : ZMod 2)) = Pi.single 11 1 := by
  decide +kernel

private theorem inverse_zero_row (x : GriessSpace) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).2.2 0 i =
      ((griessConwayEncode x).2.1 (Sum.inr (Sum.inr (0, i))) +
        ((griessConwayEncode x).2.2 0 i +
          (griessConwayEncode x).2.2 (Pi.single 11 1) i) / Real.sqrt 2) /
        Real.sqrt 2 := by
  have h := monsterNortonTensor_extra_inverse_low_coordinates x 0 i
  change (griessConwayEncode (sExtra.symm x)).2.2
    (golayLabelCoefficients (0 : Fin 4096)) i = _ at h
  have hm : golayEncodedMask 0 = 0 := by decide +kernel
  have hw : golayMaskWeight 0 = 0 := by decide +kernel
  have hz : golayLabelCoefficients (⟨0 + 2048, by omega⟩ : Fin 4096) =
      Pi.single (11 : Fin 12) (1 : ZMod 2) := omega_label
  have hn : (0 : Fin 2048).val = 0 := by decide
  simp only [hn] at h
  rw [hm, hw] at h
  have hl : golayLabelCoefficients (⟨0, by omega⟩ : Fin 4096) = 0 := zero_label
  rw [zero_label, hl, hz] at h
  simpa only [Nat.zero_testBit, Bool.false_eq_true, ite_false, Nat.zero_div,
    Nat.cast_zero, qSign_zero, one_mul] using h

/-- The inverse actual Singer lift reverses its spin and physical coordinate relabeling. -/
theorem monsterNortonSingerLocal_inverse_tensor (x : GriessSpace)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (rhoLocal monsterNortonSingerLocal⁻¹ x)).2.2 t i =
      (griessConwayEncode x).2.2 (monsterNortonSingerCode 0 t)
        (monsterNortonSingerPermutation 0 i) := by
  have h := monsterNortonSingerLocal_tensor
    (rhoLocal monsterNortonSingerLocal⁻¹ x)
    (monsterNortonSingerCode 0 t) (monsterNortonSingerPermutation 0 i)
  simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply,
    LinearEquiv.symm_apply_apply, Equiv.symm_apply_apply] at h
  exact h.symm

private theorem short_row (x : GriessSpace) (i : Fin 24) :
    (griessConwayEncode (rhoLocal monsterNortonSingerLocal x)).2.1
      (Sum.inr (Sum.inr (0, monsterNortonSingerPermutation 0 i))) =
        (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (0, i))) := by
  rw [show rhoLocal monsterNortonSingerLocal =
    localGriessRepresentation monsterNortonSingerFiber from rfl,
    localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  have h := localShortOperator_image monsterNortonSingerFiber
    (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (0, i)))
  change localShortOperator monsterNortonSingerFiber (griessConwayEncode x).2.1
    (griessShortPermutation (monsterNortonSingerPermutationIsometry 0)
      (Sum.inr (Sum.inr (0, i)))) = _ at h
  rw [monsterNortonSinger_odd_zero_permutation, monsterNortonSinger_short_phase,
    qSign_zero, one_mul] at h
  exact h

private theorem inverse_triality_row_intertwines (x : GriessSpace) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm (rhoLocal monsterNortonSingerLocal x))).2.2
      0 (monsterNortonSingerPermutation 0 i) =
        (griessConwayEncode (sExtra.symm x)).2.2 0 i := by
  rw [inverse_zero_row, inverse_zero_row, short_row,
    monsterNortonSingerLocal_tensor, monsterNortonSingerLocal_tensor]
  have ho : (monsterNortonSingerCode 0).symm (Pi.single 11 1) = Pi.single 11 1 := by
    apply (monsterNortonSingerCode 0).injective
    rw [LinearEquiv.apply_symm_apply, singer_omega]
  rw [map_zero, ho, Equiv.symm_apply_apply]

/-- The genuine Singer-triality commutator fixes the delta-zero tensor coefficient. -/
theorem monsterNortonSinger_triality_coefficient :
    (griessConwayEncode
      ((localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
        localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated).val
          monsterNortonTwentyThreeTensorVector)).2.2 0 0 = 1 := by
  change (griessConwayEncode (rhoLocal monsterNortonSingerLocal⁻¹
    (sExtra.symm (rhoLocal monsterNortonSingerLocal
      (sExtra monsterNortonTwentyThreeTensorVector))))).2.2 0 0 = 1
  rw [monsterNortonSingerLocal_inverse_tensor, map_zero,
    inverse_triality_row_intertwines, LinearEquiv.symm_apply_apply,
    monsterNortonTwentyThreeTensorVector_encode]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
