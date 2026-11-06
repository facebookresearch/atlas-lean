/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthTensorParity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQFastBinding
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEleventhRepresentative

/-! Every original Fifth tensor candidate image excludes the actual anti-Omega fixer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Check all32 original tensor candidates under the entire genuine local source word.
/-- Every complete original candidate image differs in an actual quotient coordinate. -/
theorem generatedEleventh_tensor_candidate_image_coordinates : ∀ b : ZMod 2, ∀ j : Fin 16,
    ¬(∀ i : Fin 24, toAdd
        (generatedAxisGlobalFifthQFast 3 (generatedFifthQCandidate b j)).base i =
          toAdd generatedTenthTensorAntiOmega.base i) := by
  decide +kernel

/-- Every complete actual candidate image differs from the original anti-Omega element. -/
theorem generatedEleventh_tensor_candidate_images_exclude (b : ZMod 2) (j : Fin 16) :
    generatedTenthQWordImage 3 7 (generatedFifthQCandidate b j) ≠
      generatedTenthTensorAntiOmega := by
  intro he
  rw [generatedTenth_Q_word_fast 3 generatedAxisGlobalFifthQCache03_actual] at he
  apply generatedEleventh_tensor_candidate_image_coordinates b j
  rw [he]
  exact fun _ => rfl

/-- Some original odd-short coefficient in the full actual outgoing axis is genuinely nonzero. -/
theorem generatedEleventh_odd_short_exists_nonzero : ∃ d : Fin 2048, ∃ i : Fin 24,
    (griessConwayEncode generatedEleventhAxis).2.1 (Sum.inr (Sum.inr (d, i))) ≠ 0 := by
  rw [generatedEleventhAxis_local_expression, generatedEleventhLocal]
  exact generatedTenth_odd_nonzero_of_candidate_images 3
    generatedEleventh_tensor_candidate_images_exclude

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
