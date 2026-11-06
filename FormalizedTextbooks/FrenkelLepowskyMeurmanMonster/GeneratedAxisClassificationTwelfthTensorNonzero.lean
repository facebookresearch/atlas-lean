/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthOddNonzero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthTensorFixation

/-! The same full original candidate test detects a genuine nonzero entire outgoing tensor. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every genuine original candidate image also differs from the actual positive Omega element. -/
theorem generatedTwelfth_tensor_candidate_images_exclude_Omega (b : ZMod 2) (j : Fin 16) :
    generatedTenthQWordImage 9 7 (generatedFifthQCandidate b j) ≠ sourceOmegaQ := by
  intro he
  rw [generatedTenth_Q_word_fast 9 generatedAxisGlobalFifthQCache09_actual] at he
  apply generatedTwelfth_tensor_candidate_image_coordinates b j
  have hb : generatedTenthTensorAntiOmega.base = sourceOmegaQ.base := by
    change (qCentral 1 * sourceOmegaQ).base = sourceOmegaQ.base
    exact qCentral_mul_base 1 sourceOmegaQ
  rw [he, hb]
  exact fun _ => rfl

/-- The entire genuine original outgoing twelfth tensor is nonzero. -/
theorem generatedTwelfth_tensor_ne_zero :
    (griessConwayEncode generatedTwelfthAxis).2.2 ≠ 0 := by
  rw [generatedTwelfthAxis_local_expression, generatedTwelfthLocal]
  exact generatedTenth_tensor_nonzero_of_candidate_images 9
    generatedTwelfth_tensor_candidate_images_exclude_Omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
