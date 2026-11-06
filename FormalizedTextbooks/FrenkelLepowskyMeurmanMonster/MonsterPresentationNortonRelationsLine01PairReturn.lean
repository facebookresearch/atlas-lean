/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact final V, extra, V return of the first original short-pair unit. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01PairTwelfthV

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The twelfth actual operator gives the exact original negative A,B combination. -/
theorem monsterNortonLine01PairTwelfth_actual :
    y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val
      (sExtra.symm (y555NortonActualU.val monsterNortonLine01PairAfterSeventh)))) =
      (-1 / 2 : ℝ) • trialityABCBasis 0 (monsterNortonLine01AdjacentPair 0) +
        (-1 / 2 : ℝ) • trialityABCBasis 1 (monsterNortonLine01AdjacentPair 0) := by
  rw [monsterNortonLine01PairEleventh_actual, map_add, map_smul,
    monsterNortonLine01PairV_A, map_smul, monsterNortonLine01PairV_C,
    smul_neg, ← neg_smul]
  module

/-- The thirteenth actual operator gives precisely minus the original first-pair short unit. -/
theorem monsterNortonLine01PairThirteenth_actual :
    sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val
      (sExtra.symm (y555NortonActualU.val monsterNortonLine01PairAfterSeventh))))) =
      -monsterNortonPureShort (Sum.inl (0, monsterNortonLine01AdjacentPair 0)) := by
  rw [monsterNortonLine01PairTwelfth_actual, map_add, map_smul, map_smul,
    sExtra_ABC_basis, sExtra_ABC_basis, monsterNortonPairShort_ABC]
  change (-1 / 2 : ℝ) • trialityABCBasis 1 (monsterNortonLine01AdjacentPair 0) +
    (-1 / 2 : ℝ) • trialityABCBasis 2 (monsterNortonLine01AdjacentPair 0) = _
  simp only [ite_true]
  module

/-- The final actual V operator returns the entire original first-pair short unit. -/
theorem monsterNortonLine01PairFourteenth_actual :
    y555NortonV.val (sExtra (y555NortonV.val ((y555NortonActualU⁻¹).val (y555NortonV.val
      (sExtra.symm (y555NortonActualU.val monsterNortonLine01PairAfterSeventh)))))) =
      monsterNortonPureShort (Sum.inl (0, monsterNortonLine01AdjacentPair 0)) := by
  rw [monsterNortonLine01PairThirteenth_actual, map_neg, monsterNortonLine01PairV_unit]
  simp only [ite_true, qSign_one, neg_one_smul, neg_neg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
