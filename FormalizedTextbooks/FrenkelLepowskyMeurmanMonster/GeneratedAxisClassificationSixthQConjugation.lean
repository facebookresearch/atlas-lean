/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthQWord

/-! The three cached transitions are conjugations of the original preferred short lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The checked successor equations evaluate the full original Q coordinate formula. -/
theorem generatedSixth_q_cache_image (j : Fin 3) :
    generatedSixthQImage (generatedSixthQCache j 0) = generatedSixthQCache j 8 := by
  rcases generatedSixth_q_cache_certificate j with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  unfold generatedSixthQImage generatedSixthQWord
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8]

/-- Each selected pair row has exact preferred-Q transport and no hidden central sign. -/
theorem generatedSixth_preferred_pair_transport (j : Fin 3) :
    spinConjugation generatedSixthLocalFiber.val.1
      (griessShortQ (Sum.inl (0, generatedSixthSourcePair j))) =
        griessShortQ (Sum.inl (0, generatedSixthTargetPair j)) := by
  rw [← generatedSixth_q_cache_initial, generatedSixth_spin_conjugation,
    generatedSixth_q_cache_image, generatedSixth_q_cache_final]

/-- The original short-coordinate action has precisely central phase zero on these rows. -/
theorem generatedSixth_pair_phase (j : Fin 3) :
    localShortPhase generatedSixthLocalFiber (Sum.inl (0, generatedSixthSourcePair j)) = 0 := by
  unfold localShortPhase
  rw [generatedSixth_preferred_pair_transport, griessShortQ_coeff]

/-- Their target labels are those of the actual, unchanged signed short-coordinate action. -/
theorem generatedSixth_pair_permutation (j : Fin 3) :
    griessShortPermutation generatedSixthLocalFiber.val.2
      (Sum.inl (0, generatedSixthSourcePair j)) =
        Sum.inl (0, generatedSixthTargetPair j) := by
  have hb := griessShortQ_image_base generatedSixthLocalFiber
    (Sum.inl (0, generatedSixthSourcePair j))
  rw [generatedSixth_preferred_pair_transport] at hb
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact (congrArg Multiplicative.toAdd hb).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
