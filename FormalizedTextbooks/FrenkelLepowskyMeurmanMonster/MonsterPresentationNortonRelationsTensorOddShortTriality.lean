/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact physical odd-short rows obtained from tensor coordinates by positive triality. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorTrialityCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every positive-triality odd-short coordinate is the actual previous source Z coordinate. -/
theorem monsterNortonTensor_extra_odd_short_coordinates
    (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inr (d, i))) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) /
            Real.sqrt 2 := by
  change (trialityBlocksEquiv (sExtra x)).2.2.2 0 (finProdFinEquiv (d, i)) = _
  rw [monsterTriality_XYZ_blocks, show trialityCycle.symm 0 = 2 by decide,
    monsterNortonTensor_dictionary_Z]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
