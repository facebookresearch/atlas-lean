/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceData

/-! The eleven actual lower source words avoid the unused scalar sign representative. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxHeartbeats 8000000 in
-- Check all primitive letters of all eleven complete source words without omitting inverses.
/-- Every concrete lower source word avoids primitive 11, including all inverse letters. -/
theorem generatedNinth_lower_spin_source_scalar_free : ∀ i : Fin 11,
    (generatedNinthLowerSpinSourceWord i).all (fun l => l.1 != (11 : Fin 15)) = true := by
  decide +kernel

/-- No signed source letter in any actual lower word uses the scalar primitive. -/
theorem generatedNinth_lower_spin_source_letter_ne_scalar (i : Fin 11)
    (l : GeneratedNinthLowerSpinLetter) (h : l ∈ generatedNinthLowerSpinSourceWord i) :
    l.1 ≠ (11 : Fin 15) := by
  have ha := (List.all_eq_true.mp (generatedNinth_lower_spin_source_scalar_free i)) l h
  simpa only [bne_iff_ne] using ha

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
