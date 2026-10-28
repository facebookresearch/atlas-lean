/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal first-line difference square fixes the complete second preferred short pair. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortSecondHalfNormPairing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem v_inverse : y555NortonV⁻¹ = y555NortonV := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_two, y555NortonV_square]

private theorem difference_word :
    y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 1)⁻¹ =
      y555NortonV * extraIntoGenerated * y555NortonV * y555NortonActualU⁻¹ *
        y555NortonV * extraIntoGenerated⁻¹ * y555NortonActualU * y555NortonV := by
  unfold y555NortonLine y555NortonConjugate
  change y555NortonV * ((y555NortonActualU ^ (0 : Fin 13).val)⁻¹ *
      (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (0 : Fin 13).val)⁻¹ *
    (y555NortonV * ((y555NortonActualU ^ (1 : Fin 13).val)⁻¹ *
      (y555NortonV * monsterSourceTriality) * y555NortonActualU ^ (1 : Fin 13).val)⁻¹)⁻¹ = _
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, inv_one, one_mul, mul_one,
    monsterSourceTriality, mul_inv_rev, inv_inv, v_inverse]
  group

private theorem inverse_word :
    (y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 1)⁻¹)⁻¹ =
      y555NortonV * y555NortonActualU⁻¹ * extraIntoGenerated * y555NortonV *
        y555NortonActualU * y555NortonV * extraIntoGenerated⁻¹ * y555NortonV := by
  rw [difference_word]
  simp only [mul_inv_rev, inv_inv, v_inverse]
  group

private theorem generated_mul_apply (a b : G) (x : GriessSpace) :
    (a * b).val x = a.val (b.val x) := rfl

private theorem generated_inverse_apply (g : G) (x : GriessSpace) :
    g.val ((g⁻¹).val x) = x :=
  LinearEquiv.apply_symm_apply _ _

/-- Both entire literal half images have exact maximal pairing on the second preferred pair. -/
theorem monsterNortonLineZeroOne_second_pair_halves :
    griessForm ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 1)))
      (((y555NortonLine monsterSourceTriality 0 *
        (y555NortonLine monsterSourceTriality 1)⁻¹)⁻¹).val
          (monsterNortonPureShort (monsterNortonEvenShortBasis 1))) = 1 := by
  rw [inverse_word, difference_word]
  simp only [generated_mul_apply]
  change griessForm
    (y555NortonV.val (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val
      (sExtra.symm (y555NortonActualU.val (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 1))))))))))
    (y555NortonV.val ((y555NortonActualU⁻¹).val (sExtra (y555NortonV.val
      (y555NortonActualU.val (y555NortonV.val (sExtra.symm (y555NortonV.val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 1)))))))))) = 1
  rw [generated_group_preserves_griessForm y555NortonV,
    monsterNortonEvenShortSecondHalf_actual, monsterNortonEvenShortSecondInverseFirstSix_actual]
  have h := generated_group_preserves_griessForm y555NortonActualU
    monsterNortonSecondHalfPacket
    ((y555NortonActualU⁻¹).val monsterNortonEvenShortSecondInverseSixthPacket)
  rw [generated_inverse_apply] at h
  rw [← h]
  exact monsterNortonSecondHalfU_pairing_one

/-- The literal first-line difference square fixes the entire genuine pair
at coordinates zero and two. -/
theorem monsterNortonLineZeroOneSquare_second_pair_fixed :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort (monsterNortonEvenShortBasis 1)) =
      monsterNortonPureShort (monsterNortonEvenShortBasis 1) :=
  monsterNortonGenerated_square_short_fixed_of_halves _ _
    monsterNortonLineZeroOne_second_pair_halves

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
