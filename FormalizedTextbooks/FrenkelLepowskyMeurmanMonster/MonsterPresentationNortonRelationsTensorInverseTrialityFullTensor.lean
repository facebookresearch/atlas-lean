/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full genuine inverse-triality tensor action in the original physical coordinates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorInverseTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full original inverse-triality tensor formula, retaining both physical halves. -/
noncomputable def monsterNortonTensorInverseTrialityCoordinates
    (X : GriessShortIndex → ℝ) (T : SpinIndex → Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) : ℝ :=
  let d := spinDictionaryCode t
  (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
      X (Sum.inr (Sum.inr (d, i))) +
    qSign (t 11) * (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1) *
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        (T (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          T (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) / Real.sqrt 2)) / Real.sqrt 2

/-- This is the entire tensor action of actual inverse triality on every Griess vector. -/
theorem monsterNortonTensorInverseTrialityCoordinates_actual (x : GriessSpace)
    (t : SpinIndex) (i : Fin 24) :
    (griessConwayEncode (sExtra.symm x)).2.2 t i =
      monsterNortonTensorInverseTrialityCoordinates
        (griessConwayEncode x).2.1 (griessConwayEncode x).2.2 t i := by
  change (qSign _ * (trialityBlocksEquiv (sExtra.symm x)).2.2.2 2 _ +
    qSign (t 11) * _ * (trialityBlocksEquiv (sExtra.symm x)).2.2.2 1 _) / _ = _
  rw [monsterNortonTensor_inverse_XYZ, monsterNortonTensor_inverse_XYZ,
    show trialityCycle 2 = 0 by decide, show trialityCycle 1 = 2 by decide,
    monsterNortonTensor_dictionary_Z]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
