/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSeventhQWord

/-! The three cached transitions are conjugations of the original preferred short lifts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The checked successor equations evaluate the full original Q coordinate formula. -/
theorem generatedSeventh_q_cache_image (j : Fin 3) :
    generatedSeventhQImage (generatedSeventhQCache j 0) = generatedSeventhQCache j 7 := by
  rcases generatedSeventh_q_cache_certificate j with ⟨h1, h2, h3, h4, h5, h6, h7⟩
  unfold generatedSeventhQImage generatedSeventhQWord
  simp only [List.foldl_cons, List.foldl_nil]
  rw [← h1, ← h2, ← h3, ← h4, ← h5, ← h6, ← h7]

/-- Each selected pair row has exact preferred-Q transport and no hidden central sign. -/
theorem generatedSeventh_preferred_pair_transport (j : Fin 3) :
    spinConjugation generatedSeventhLocalFiber.val.1
      (griessShortQ (Sum.inl (0, generatedSeventhSourcePair j))) =
        griessShortQ (Sum.inl (0, generatedSeventhTargetPair j)) := by
  rw [← generatedSeventh_q_cache_initial, generatedSeventh_spin_conjugation,
    generatedSeventh_q_cache_image, generatedSeventh_q_cache_final]

/-- The original short-coordinate action has precisely central phase zero on these rows. -/
theorem generatedSeventh_pair_phase (j : Fin 3) :
    localShortPhase generatedSeventhLocalFiber (Sum.inl (0, generatedSeventhSourcePair j)) = 0 := by
  unfold localShortPhase
  rw [generatedSeventh_preferred_pair_transport, griessShortQ_coeff]

/-- Their target labels are those of the actual, unchanged signed short-coordinate action. -/
theorem generatedSeventh_pair_permutation (j : Fin 3) :
    griessShortPermutation generatedSeventhLocalFiber.val.2
      (Sum.inl (0, generatedSeventhSourcePair j)) =
        Sum.inl (0, generatedSeventhTargetPair j) := by
  have hb := griessShortQ_image_base generatedSeventhLocalFiber
    (Sum.inl (0, generatedSeventhSourcePair j))
  rw [generatedSeventh_preferred_pair_transport] at hb
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  exact (congrArg Multiplicative.toAdd hb).symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
