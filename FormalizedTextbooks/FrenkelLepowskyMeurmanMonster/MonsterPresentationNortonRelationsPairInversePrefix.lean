/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact literal V, inverse-triality, V prefixes on all preferred physical pair units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairMatrixUTwo
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsPairTrialityInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsEvenShortFourth

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The whole B basis vector is the exact difference of the two preferred pair units. -/
theorem monsterNortonPairB_short_difference (p : Fin 276) :
    trialityABCBasis 1 p = monsterNortonPureShort (Sum.inl (0, p)) -
      monsterNortonPureShort (Sum.inl (1, p)) := by
  rw [monsterNortonPairShort_ABC, monsterNortonPairShort_ABC]
  norm_num
  module

/-- The whole C basis vector is precisely the sum of the two preferred pair units. -/
theorem monsterNortonPairC_short_sum (p : Fin 276) :
    trialityABCBasis 2 p = monsterNortonPureShort (Sum.inl (0, p)) +
      monsterNortonPureShort (Sum.inl (1, p)) := by
  rw [monsterNortonPairShort_ABC, monsterNortonPairShort_ABC]
  norm_num
  module

/-- Literal V keeps both actual short signs when applied to the entire physical B coordinate. -/
theorem monsterNortonV_pair_B (p : Fin 276) :
    y555NortonV.val (trialityABCBasis 1 p) =
      qSign (monsterNortonVShortPhase (Sum.inl (0, p))) •
        monsterNortonPureShort (Sum.inl (0, p)) -
      qSign (monsterNortonVShortPhase (Sum.inl (1, p))) •
        monsterNortonPureShort (Sum.inl (1, p)) := by
  rw [monsterNortonPairB_short_difference, map_sub,
    monsterNortonV_pure_short, monsterNortonV_pure_short]

/-- The complete first three inverse-half states keep the original pair phase and pure matrix. -/
theorem monsterNortonPairInversePrefix_actual (s : Fin 2) (p : Fin 276) :
    y555NortonV.val (sExtra.symm (y555NortonV.val
      (monsterNortonPureShort (Sum.inl (s, p))))) =
    qSign (monsterNortonVShortPhase (Sum.inl (s, p))) •
      ((1 / 2 : ℝ) •
        (qSign (monsterNortonVShortPhase (Sum.inl (0, p))) •
          monsterNortonPureShort (Sum.inl (0, p)) -
        qSign (monsterNortonVShortPhase (Sum.inl (1, p))) •
          monsterNortonPureShort (Sum.inl (1, p))) +
      (if s = 0 then (1 / 2 : ℝ) else -1 / 2) • trialityABCBasis 0 p) := by
  rw [monsterNortonV_pure_short, map_smul, map_smul, monsterNortonPairShort_extra_inverse,
    map_add, map_smul, map_smul, monsterNortonV_pair_B]
  have hA : y555NortonV.val (trialityABCBasis 0 p) = trialityABCBasis 0 p := by
    rw [y555NortonV]
    exact monsterNortonQ_pair_matrix y555NortonVQ p
  rw [hA]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
