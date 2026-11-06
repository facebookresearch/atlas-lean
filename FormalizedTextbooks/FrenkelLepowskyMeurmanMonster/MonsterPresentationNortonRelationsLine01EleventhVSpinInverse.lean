/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual inverse spin transport from the checked finite coefficient certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhVSpinInverseCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem zero_supported : monsterNortonLine01CompactOutputSupport 0 := by
  decide +kernel

private theorem omega_supported : monsterNortonLine01CompactOutputSupport 2048 := by
  decide +kernel

/-- The inverse equality holds at every genuine spin label, including the zero complement. -/
theorem monsterNortonLine01EleventhVSpin_inverse_actual (n : Fin 4096) :
    monsterNortonUCompactInverseNumerator monsterNortonLine01EleventhVSpinVector n =
      32 * monsterNortonLine01ThirteenthSpinVector n := by
  by_cases hn : monsterNortonLine01CompactOutputSupport n
  · have he : monsterNortonLine01CompactOutputLabel
        (monsterNortonLine01CompactOutputLookup n) = n := hn
    exact (congrArg (monsterNortonUCompactInverseNumerator
      monsterNortonLine01EleventhVSpinVector) he).symm.trans
        ((monsterNortonLine01EleventhVSpin_inverse_coefficients
          (monsterNortonLine01CompactOutputLookup n)).trans
            (congrArg (fun m => 32 * monsterNortonLine01ThirteenthSpinVector m) he))
  · have h0 : n ≠ 0 := by rintro rfl; exact hn zero_supported
    have h1 : n ≠ 2048 := by rintro rfl; exact hn omega_supported
    rw [monsterNortonLine01EleventhVSpin_inverse_zero n hn]
    simp [monsterNortonLine01ThirteenthSpinVector, h0, h1]

/-- The actual inverse spin factor has the exact negative scalar on the two surviving deltas. -/
theorem monsterNortonLine01EleventhVSpin_inverse_embed :
    (monsterNortonUFiber.val.1⁻¹).val
      (nortonUIntegerEmbed monsterNortonLine01EleventhVSpinVector) =
        (-4 : ℝ) • nortonUIntegerEmbed monsterNortonLine01ThirteenthSpinVector := by
  rw [monsterNortonUCompactInverseSpin_actual_embed]
  ext t
  simp only [Pi.smul_apply, smul_eq_mul, nortonUIntegerEmbed]
  rw [monsterNortonLine01EleventhVSpin_inverse_actual]
  push_cast
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
