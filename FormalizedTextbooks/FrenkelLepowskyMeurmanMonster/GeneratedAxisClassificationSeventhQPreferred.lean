/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhPairData

/-! The three cached transitions are conjugations of the original preferred short lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem pair_Q (p : Fin 276) :
    generatedAxisFourthQFromSpin 0 (griessPairSyndrome p) 0 =
      griessShortQ (Sum.inl (0, p)) := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation, griessPairQ_translation]
    rfl
  · rw [generatedAxisFourthQFromSpin_modulation, griessPairQ_modulation]
  · rw [generatedAxisFourthQFromSpin_coeff, griessShortQ_coeff]

/-- The initial cache entries are the actual preferred source short lifts. -/
theorem generatedSeventh_q_cache_initial (j : Fin 3) :
    generatedSeventhQCache j 0 = griessShortQ (Sum.inl (0, generatedSeventhSourcePair j)) := by
  rw [← pair_Q, (generatedSeventh_pair_syndrome_certificate j).1]
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

/-- The final cache entries are the actual preferred target lifts with central coefficient zero. -/
theorem generatedSeventh_q_cache_final (j : Fin 3) :
    generatedSeventhQCache j 7 = griessShortQ (Sum.inl (0, generatedSeventhTargetPair j)) := by
  rw [← pair_Q, (generatedSeventh_pair_syndrome_certificate j).2]
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
