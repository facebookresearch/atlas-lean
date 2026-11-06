/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- One entire nonzero Griess tensor vector fixed by the literal first line-difference square. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01Closing

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

private theorem square_word :
    (y555NortonLine monsterSourceTriality 0 * (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2 =
      y555NortonV * extraIntoGenerated * y555NortonV * y555NortonActualU⁻¹ *
        y555NortonV * extraIntoGenerated⁻¹ * y555NortonActualU * extraIntoGenerated *
          y555NortonV * y555NortonActualU⁻¹ * y555NortonV * extraIntoGenerated⁻¹ *
            y555NortonActualU * y555NortonV := by
  calc
    _ = y555NortonV * extraIntoGenerated * y555NortonV * y555NortonActualU⁻¹ *
        y555NortonV * extraIntoGenerated⁻¹ * y555NortonActualU *
          (y555NortonV * y555NortonV) * extraIntoGenerated * y555NortonV *
            y555NortonActualU⁻¹ * y555NortonV * extraIntoGenerated⁻¹ *
              y555NortonActualU * y555NortonV := by
      rw [difference_word, pow_two]
      group
    _ = _ := by rw [← pow_two, y555NortonV_square]; group

private theorem generated_mul_apply (a b : G) (x : GriessSpace) :
    (a * b).val x = a.val (b.val x) := rfl

/-- The square of the literal first line difference fixes this entire genuine nonzero input.
This is the tensor-vector test; further commutation tests are needed for group identity. -/
theorem monsterNortonLineZeroOneSquare_tensor_fixed :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val monsterNortonLine01TensorStart =
        monsterNortonLine01TensorStart := by
  rw [square_word]
  simp only [generated_mul_apply]
  change y555NortonV.val (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val
    (y555NortonV.val (sExtra.symm (y555NortonActualU.val (sExtra (y555NortonV.val
      ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
        (y555NortonActualU.val (y555NortonV.val monsterNortonLine01TensorStart))))))))))))) = _
  rw [monsterNortonLine01TensorV_actual, monsterNortonLine01TensorU_actual,
    monsterNortonLine01TensorExtraInverse_actual, monsterNortonLine01TensorVSource_actual,
    monsterNortonLine01TensorInverseU_actual, monsterNortonLine01TensorSecondV_actual,
    monsterNortonLine01Eleventh_actual, monsterNortonLine01Twelfth_actual,
    monsterNortonLine01Thirteenth_actual, monsterNortonLine01Fourteenth_actual,
    monsterNortonLine01Fifteenth_actual, monsterNortonLine01Sixteenth_actual]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
