/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityCoordinates

/-! Actual positive triality on arbitrary physical pair-short and matrix coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual A row is its original off-diagonal physical matrix entry. -/
theorem generatedNinth_dictionary_A (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv x).2.1 0 p =
      (griessConwayEncode x).1 (griessCoordinatePair p).1 (griessCoordinatePair p).2 := by
  have h := congrArg (fun y : GriessSpace => (trialityBlocksEquiv y).2.1 0 p)
    (griessConwayDecode_encode x)
  simpa only [griessConwayDecode, LinearEquiv.apply_symm_apply, ite_true] using h.symm

/-- The actual B row is half the difference of the two physical signed-pair rows. -/
theorem generatedNinth_dictionary_B (x : GriessSpace) (p : Fin 276) :
    (trialityBlocksEquiv x).2.1 1 p =
      ((griessConwayEncode x).2.1 (Sum.inl (0, p)) -
        (griessConwayEncode x).2.1 (Sum.inl (1, p))) / 2 := by
  have h := congrArg (fun y : GriessSpace => (trialityBlocksEquiv y).2.1 1 p)
    (griessConwayDecode_encode x)
  simpa only [griessConwayDecode, LinearEquiv.apply_symm_apply,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, ite_true] using h.symm

/-- Every final physical pair row has the old B row and its signed original matrix entry. -/
theorem generatedNinth_final_triality_pair_coordinate
    (x : GriessSpace) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inl (s, p)) =
      ((griessConwayEncode x).2.1 (Sum.inl (0, p)) -
        (griessConwayEncode x).2.1 (Sum.inl (1, p))) / 2 +
      (if s = 0 then
        (griessConwayEncode x).1 (griessCoordinatePair p).1 (griessCoordinatePair p).2
      else -(griessConwayEncode x).1
        (griessCoordinatePair p).1 (griessCoordinatePair p).2) := by
  change (if s = 0 then
    (trialityBlocksEquiv (sExtra x)).2.1 1 p + (trialityBlocksEquiv (sExtra x)).2.1 2 p
    else (trialityBlocksEquiv (sExtra x)).2.1 2 p -
      (trialityBlocksEquiv (sExtra x)).2.1 1 p) = _
  rw [monsterTriality_ABC_blocks, monsterTriality_ABC_blocks]
  simp only [show trialityCycle.symm 1 = 0 by decide,
    show trialityCycle.symm 2 = 1 by decide, generatedNinth_dictionary_A,
    generatedNinth_dictionary_B]
  split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
