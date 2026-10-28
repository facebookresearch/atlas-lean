/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal first-line difference square fixes an actual short unit and belongs to H. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairReturn
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsGlobalShortIdentity

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


private theorem pairInput_eq :
    monsterNortonLine01PairShortInput = Sum.inl (0, monsterNortonLine01AdjacentPair 0) := by
  unfold monsterNortonLine01PairShortInput monsterNortonLine01AdjacentPair
  rfl

/-- The literal first line-difference square fixes the whole genuine first short-pair unit. -/
theorem monsterNortonLineZeroOneSquare_pair_fixed :
    ((y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2).val
        (monsterNortonPureShort monsterNortonLine01PairShortInput) =
      monsterNortonPureShort monsterNortonLine01PairShortInput := by
  rw [square_word]
  simp only [generated_mul_apply]
  change y555NortonV.val (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val
    (y555NortonV.val (sExtra.symm (y555NortonActualU.val (sExtra (y555NortonV.val
      ((y555NortonActualU⁻¹).val (y555NortonV.val (sExtra.symm
        (y555NortonActualU.val (y555NortonV.val
          (monsterNortonPureShort monsterNortonLine01PairShortInput)))))))))))))) = _
  rw [monsterNortonLine01PairSeventh_literal, monsterNortonLine01PairFourteenth_actual,
    pairInput_eq]

/-- The literal first line-difference square itself lies in the actual local subgroup H. -/
theorem monsterNortonLineZeroOneSquare_mem_local :
    (y555NortonLine monsterSourceTriality 0 *
      (y555NortonLine monsterSourceTriality 1)⁻¹) ^ 2 ∈ localIntoGenerated.range :=
  monsterNortonGenerated_fix_short_mem_local _ _ monsterNortonLineZeroOneSquare_pair_fixed

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
