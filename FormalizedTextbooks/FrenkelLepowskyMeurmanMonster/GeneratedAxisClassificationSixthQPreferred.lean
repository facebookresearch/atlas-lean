/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthPairData

/-! The three cached transitions are conjugations of the original preferred short lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem pair_Q (p : Fin 276) :
    generatedAxisFourthQFromSpin 0 (griessPairSyndrome p) 0 =
      griessShortQ (Sum.inl (0, p)) := by
  apply generatedAxisFourthQ_spin_coordinates_injective
  · rw [generatedAxisFourthQFromSpin_translation, griessPairQ_translation]
    rfl
  · rw [generatedAxisFourthQFromSpin_modulation, griessPairQ_modulation]
  · rw [generatedAxisFourthQFromSpin_coeff, griessShortQ_coeff]

/-- The initial cache entries are the actual preferred source short lifts. -/
theorem generatedSixth_q_cache_initial (j : Fin 3) :
    generatedSixthQCache j 0 = griessShortQ (Sum.inl (0, generatedSixthSourcePair j)) := by
  rw [← pair_Q, (generatedSixth_pair_syndrome_certificate j).1]
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

/-- The final cache entries are the actual preferred target lifts with central coefficient zero. -/
theorem generatedSixth_q_cache_final (j : Fin 3) :
    generatedSixthQCache j 8 = griessShortQ (Sum.inl (0, generatedSixthTargetPair j)) := by
  rw [← pair_Q, (generatedSixth_pair_syndrome_certificate j).2]
  fin_cases j <;> apply NormalizedCocycleExtension.Extension.ext
  all_goals decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
