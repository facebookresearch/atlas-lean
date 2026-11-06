/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Literal line-word return reduction through complete actual forward and inverse packets. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01ReturnFromPackets

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The actual squared Norton element used in the distance-two word. -/
noncomputable def monsterNortonDistanceTwoU : G := y555NortonActualU ^ 2

private theorem v_inverse : y555NortonV⁻¹ = y555NortonV := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two, y555NortonV_square]

private theorem difference_word :
    y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 2)⁻¹ =
      y555NortonV * extraIntoGenerated * y555NortonV * monsterNortonDistanceTwoU⁻¹ *
        y555NortonV * extraIntoGenerated⁻¹ * monsterNortonDistanceTwoU * y555NortonV := by
  unfold y555NortonLine y555NortonConjugate
  change y555NortonV * ((y555NortonActualU ^ (0 : ℕ))⁻¹ *
      (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (0 : ℕ))⁻¹ *
    (y555NortonV * ((y555NortonActualU ^ (2 : ℕ))⁻¹ *
      (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (2 : ℕ))⁻¹)⁻¹ = _
  simp only [pow_zero, inv_one, one_mul, mul_one, monsterSourceTriality,
    mul_inv_rev, inv_inv, v_inverse]
  dsimp only [monsterNortonDistanceTwoU]
  group

private theorem inverse_word :
    (y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 2)⁻¹)⁻¹ =
      y555NortonV * monsterNortonDistanceTwoU⁻¹ * extraIntoGenerated * y555NortonV *
        monsterNortonDistanceTwoU * y555NortonV * extraIntoGenerated⁻¹ * y555NortonV := by
  rw [difference_word]
  simp only [mul_inv_rev, inv_inv, v_inverse]
  group

private theorem generated_mul_apply (a b : G) (x : GriessSpace) :
    (a * b).val x = a.val (b.val x) := rfl

private theorem generated_inverse_apply (g : G) (x : GriessSpace) :
    g.val ((g⁻¹).val x) = x :=
  LinearEquiv.apply_symm_apply _ _

/-- Complete actual distance-two packet bindings and maximal pairing give a whole literal return. -/
theorem monsterNortonLineZeroTwo_square_return_of_packets (r : GriessShortIndex)
    (A B : GriessSpace)
    (hf : sExtra (y555NortonV.val ((monsterNortonDistanceTwoU⁻¹).val (y555NortonV.val
      (sExtra.symm (monsterNortonDistanceTwoU.val (y555NortonV.val
        (monsterNortonPureShort r))))))) = A)
    (hi : sExtra (y555NortonV.val (monsterNortonDistanceTwoU.val (y555NortonV.val
      (sExtra.symm (y555NortonV.val (monsterNortonPureShort r)))))) = B)
    (hp : griessForm (monsterNortonDistanceTwoU.val A) B = 1) :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 2)⁻¹) ^ 2).val (monsterNortonPureShort r) =
        monsterNortonPureShort r := by
  apply monsterNortonGenerated_square_short_fixed_of_halves
  rw [inverse_word, difference_word]
  simp only [generated_mul_apply]
  change griessForm
    (y555NortonV.val (sExtra (y555NortonV.val ((monsterNortonDistanceTwoU⁻¹).val
      (y555NortonV.val (sExtra.symm (monsterNortonDistanceTwoU.val
        (y555NortonV.val (monsterNortonPureShort r)))))))))
    (y555NortonV.val ((monsterNortonDistanceTwoU⁻¹).val (sExtra (y555NortonV.val
      (monsterNortonDistanceTwoU.val (y555NortonV.val (sExtra.symm
        (y555NortonV.val (monsterNortonPureShort r))))))))) = 1
  rw [generated_group_preserves_griessForm y555NortonV, hf, hi]
  have h := generated_group_preserves_griessForm monsterNortonDistanceTwoU A
    ((monsterNortonDistanceTwoU⁻¹).val B)
  rw [generated_inverse_apply] at h
  rw [← h]
  exact hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
