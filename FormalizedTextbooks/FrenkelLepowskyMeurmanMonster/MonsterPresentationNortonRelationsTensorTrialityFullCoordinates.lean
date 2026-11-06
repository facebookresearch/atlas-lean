/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete physical tensor dictionary for actual positive triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original positive-triality physical tensor formula for arbitrary short and tensor rows. -/
noncomputable def monsterNortonTensorTrialityCoordinates (X : GriessShortIndex → ℝ)
    (T : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) : ℝ :=
  let d := spinDictionaryCode t
  let sign := if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1
  (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      (sign * (T (golayLabelCoefficients ⟨d.val, by omega⟩) i -
        T (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2) +
    qSign (t 11) * sign * X (Sum.inr (Sum.inr (d, i)))) / Real.sqrt 2

/-- Every physical tensor coordinate of actual positive triality is given by this source formula. -/
theorem monsterNortonTensorTrialityCoordinates_actual (x : GriessSpace) (t : SpinIndex)
    (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.2 t i =
      monsterNortonTensorTrialityCoordinates (griessConwayEncode x).2.1
        (griessConwayEncode x).2.2 t i := by
  change (qSign _ * (trialityBlocksEquiv (sExtra x)).2.2.2 2 _ +
    qSign (t 11) * _ * (trialityBlocksEquiv (sExtra x)).2.2.2 1 _) / _ = _
  rw [monsterTriality_XYZ_blocks, monsterTriality_XYZ_blocks,
    show trialityCycle.symm 2 = 1 by decide, show trialityCycle.symm 1 = 0 by decide,
    monsterNortonTensor_dictionary_Y]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
