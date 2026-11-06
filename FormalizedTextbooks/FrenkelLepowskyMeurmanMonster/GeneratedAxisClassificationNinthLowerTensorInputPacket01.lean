/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorSourceCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorBoundedQuantifier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinTensorInputData

/-! All4096 original spin labels in spatial column1 retain the complete XYZ source formula. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

set_option maxHeartbeats 16000000 in
-- Compare every original label in this entire column against both source contributions.
/-- The complete normalized input cache in column1 is the original XYZ numerator. -/
theorem generatedNinth_lower_tensor_input_packet_01 : ∀ n : Fin 4096,
    generatedNinthLowerSpinTensorInputInteger n 1 =
      generatedNinthLowerTensorSourceInteger n 1 := by
  apply generatedNinth_lower_spin_tensor_predicate4096_of_blocks
  simp_rw [← generatedNinth_lower_tensor_source_cached_actual]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
