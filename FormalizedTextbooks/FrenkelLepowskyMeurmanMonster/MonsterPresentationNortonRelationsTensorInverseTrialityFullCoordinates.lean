/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full physical-coordinate consequences of genuine inverse triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorInverseTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The low inverse-triality row in the original physical short and tensor coordinates. -/
theorem monsterNortonTensor_extra_inverse_low_coordinates
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i))) +
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
            ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
              (griessConwayEncode x).2.2
                (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2)) /
          Real.sqrt 2 := by
  rw [monsterNortonTensor_extra_inverse_low, monsterNortonTensor_dictionary_Z]

/-- The high inverse-triality row has the opposite old Z tensor contribution. -/
theorem monsterNortonTensor_extra_inverse_high_coordinates
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).2.2
        (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
          (griessConwayEncode x).2.1 (Sum.inr (Sum.inr (d, i))) -
        (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
          (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
            ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
              (griessConwayEncode x).2.2
                (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2)) /
          Real.sqrt 2 := by
  rw [monsterNortonTensor_extra_inverse_high, monsterNortonTensor_dictionary_Z]

private theorem zero_ABC (x : GriessSpace)
    (hM : ∀ i j, (griessConwayEncode x).1 i j = 0)
    (hP : ∀ s p, (griessConwayEncode x).2.1 (Sum.inl (s, p)) = 0)
    (s : Fin 3) (p : Fin 276) : (trialityBlocksEquiv x).2.1 s p = 0 := by
  have h := congrArg (fun y : GriessSpace => (trialityBlocksEquiv y).2.1 s p)
    (griessConwayDecode_encode x)
  fin_cases s <;> simpa [griessConwayDecode, hM, hP] using h.symm

private theorem inverse_ABC (x : GriessSpace) (s : Fin 3) (p : Fin 276) :
    (trialityBlocksEquiv (sExtra.symm x)).2.1 s p =
      (trialityBlocksEquiv x).2.1 (trialityCycle s) p :=
  monsterTriality_inverse_ABC_blocks x s p

private theorem extra_diag (x : GriessSpace) (i : Fin 24) :
    (trialityBlocksEquiv (sExtra x)).1 i = (trialityBlocksEquiv x).1 i := by
  simp only [sExtra, griessTriality, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, trialityBlockAction, LinearEquiv.prodCongr_apply]
  rfl

private theorem inverse_diag (x : GriessSpace) (i : Fin 24) :
    (trialityBlocksEquiv (sExtra.symm x)).1 i = (trialityBlocksEquiv x).1 i := by
  have h := extra_diag (sExtra.symm x) i
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The entire physical matrix remains zero under inverse triality when the pair rows vanish. -/
theorem monsterNortonTensor_extra_inverse_matrix_zero (x : GriessSpace)
    (hM : ∀ i j, (griessConwayEncode x).1 i j = 0)
    (hP : ∀ s p, (griessConwayEncode x).2.1 (Sum.inl (s, p)) = 0)
    (i j : Fin 24) : (griessConwayEncode (sExtra.symm x)).1 i j = 0 := by
  by_cases h : i = j
  · subst j
    simp only [griessConwayEncode, dite_true]
    rw [inverse_diag]
    simpa only [griessConwayEncode, dite_true] using hM i i
  · change (if he : i = j then _ else
      (trialityBlocksEquiv (sExtra.symm x)).2.1 0 (griessPairIndex i j he)) = 0
    rw [dite_eq_right h, inverse_ABC]
    exact zero_ABC x hM hP _ _

/-- Inverse triality retains zero pair-short rows when the matrix and pair rows vanish. -/
theorem monsterNortonTensor_extra_inverse_pair_short_zero (x : GriessSpace)
    (hM : ∀ i j, (griessConwayEncode x).1 i j = 0)
    (hP : ∀ s p, (griessConwayEncode x).2.1 (Sum.inl (s, p)) = 0)
    (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra.symm x)).2.1 (Sum.inl (s, p)) = 0 := by
  change (if s = 0 then
    (trialityBlocksEquiv (sExtra.symm x)).2.1 1 p + (trialityBlocksEquiv (sExtra.symm x)).2.1 2 p
    else (trialityBlocksEquiv (sExtra.symm x)).2.1 2 p -
      (trialityBlocksEquiv (sExtra.symm x)).2.1 1 p) = 0
  simp only [inverse_ABC, zero_ABC x hM hP, add_zero, sub_self, ite_self]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
