/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityCoordinates

/-! The final positive triality extracts the original physical Z row into odd-short coordinates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Z row is the quarter-weight signed sum of the physical tensor halves. -/
theorem generatedNinth_dictionary_Z (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d, i)) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          (griessConwayEncode x).2.2
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2 := by
  have h := congrArg (fun y : GriessSpace =>
    (trialityBlocksEquiv y).2.2.2 2 (finProdFinEquiv (d, i)))
    (griessConwayDecode_encode x)
  simpa only [griessConwayDecode, LinearEquiv.apply_symm_apply,
    Equiv.symm_apply_apply, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ite_false] using h.symm

/-- Every odd-short coordinate after actual positive triality receives the old Z row. -/
theorem generatedNinth_final_triality_odd_coordinate
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inr (d, i))) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          (griessConwayEncode x).2.2
            (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2 := by
  change (trialityBlocksEquiv (sExtra x)).2.2.2 0 (finProdFinEquiv (d, i)) = _
  rw [monsterTriality_XYZ_blocks, show trialityCycle.symm 0 = 2 by decide]
  exact generatedNinth_dictionary_Z x d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
