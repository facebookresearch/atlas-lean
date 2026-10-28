/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual triality preserves the zero matrix and pair-short coordinate conditions. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem zero_ABC (x : GriessSpace)
    (hM : ∀ i j, (griessConwayEncode x).1 i j = 0)
    (hP : ∀ s p, (griessConwayEncode x).2.1 (Sum.inl (s, p)) = 0)
    (s : Fin 3) (p : Fin 276) : (trialityBlocksEquiv x).2.1 s p = 0 := by
  have h := congrArg (fun y : GriessSpace => (trialityBlocksEquiv y).2.1 s p)
    (griessConwayDecode_encode x)
  fin_cases s <;> simpa [griessConwayDecode, hM, hP] using h.symm

/-- The entire physical matrix remains zero under actual triality when the pair rows vanish. -/
theorem monsterNortonTensor_extra_matrix_zero (x : GriessSpace)
    (hM : ∀ i j, (griessConwayEncode x).1 i j = 0)
    (hP : ∀ s p, (griessConwayEncode x).2.1 (Sum.inl (s, p)) = 0)
    (i j : Fin 24) : (griessConwayEncode (sExtra x)).1 i j = 0 := by
  by_cases h : i = j
  · subst j
    simp only [griessConwayEncode, dite_true]
    have hd : (trialityBlocksEquiv (sExtra x)).1 i = (trialityBlocksEquiv x).1 i := by
      simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
        LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply]
      rfl
    rw [hd]
    simpa only [griessConwayEncode, dite_true] using hM i i
  · change (if he : i = j then _ else
      (trialityBlocksEquiv (sExtra x)).2.1 0 (griessPairIndex i j he)) = 0
    rw [dite_eq_right h, monsterTriality_ABC_blocks]
    exact zero_ABC x hM hP _ _

/-- Actual triality retains zero physical pair-short rows when the matrix and pair rows vanish. -/
theorem monsterNortonTensor_extra_pair_short_zero (x : GriessSpace)
    (hM : ∀ i j, (griessConwayEncode x).1 i j = 0)
    (hP : ∀ s p, (griessConwayEncode x).2.1 (Sum.inl (s, p)) = 0)
    (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inl (s, p)) = 0 := by
  change (if s = 0 then
    (trialityBlocksEquiv (sExtra x)).2.1 1 p + (trialityBlocksEquiv (sExtra x)).2.1 2 p
    else (trialityBlocksEquiv (sExtra x)).2.1 2 p -
      (trialityBlocksEquiv (sExtra x)).2.1 1 p) = 0
  simp only [monsterTriality_ABC_blocks, zero_ABC x hM hP, add_zero, sub_self, ite_self]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
