/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual triality odd-short row vanishes for an antisymmetric physical tensor. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQSourceCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Z dictionary row is determined by the physical low/high tensor sum. -/
theorem monsterNortonTensor_dictionary_Z (x : GriessSpace) (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d, i)) =
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) *
        ((griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i +
          (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i) /
            Real.sqrt 2 := by
  have h := congrArg (fun y : GriessSpace =>
    (trialityBlocksEquiv y).2.2.2 2 (finProdFinEquiv (d, i)))
    (griessConwayDecode_encode x)
  simpa only [griessConwayDecode, LinearEquiv.apply_symm_apply,
    Equiv.symm_apply_apply, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, ite_false] using h.symm

/-- An antisymmetric physical tensor has no actual Z dictionary coordinate. -/
theorem monsterNortonTensor_dictionary_Z_zero (x : GriessSpace)
    (hanti : ∀ (d : Fin 2048) (i : Fin 24),
      (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
        -(griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i)
    (d : Fin 2048) (i : Fin 24) :
    (trialityBlocksEquiv x).2.2.2 2 (finProdFinEquiv (d, i)) = 0 := by
  rw [monsterNortonTensor_dictionary_Z, hanti, add_neg_cancel, mul_zero, zero_div]

/-- Actual positive triality contributes no odd short coordinate from an antisymmetric tensor. -/
theorem monsterNortonTensor_extra_odd_short_zero (x : GriessSpace)
    (hanti : ∀ (d : Fin 2048) (i : Fin 24),
      (griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) i =
        -(griessConwayEncode x).2.2 (golayLabelCoefficients ⟨d.val, by omega⟩) i)
    (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (sExtra x)).2.1 (Sum.inr (Sum.inr (d, i))) = 0 := by
  change (trialityBlocksEquiv (sExtra x)).2.2.2 0 (finProdFinEquiv (d, i)) = 0
  rw [monsterTriality_XYZ_blocks, show trialityCycle.symm 0 = 2 by decide]
  exact monsterNortonTensor_dictionary_Z_zero x hanti d i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
