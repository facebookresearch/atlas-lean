/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthTensorFixation
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQFastBinding
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache08
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightRepresentative

/-! The entire actual Fifth tensor stabilizer detects both nonzero root-eight triality sectors. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
-- Check every original tensor-fixing candidate under the entire genuine root-eight Q word.
/-- No original fixing candidate image has the actual Omega quotient coordinates. -/
theorem generatedFifthRootEight_tensor_candidate_image_coordinates :
    ∀ b : ZMod 2, ∀ j : Fin 16,
      ¬(∀ i : Fin 24,
        toAdd (generatedAxisGlobalFifthQFast 8 (generatedFifthQCandidate b j)).base i =
          toAdd sourceOmegaQ.base i) := by
  decide +kernel

/-- The complete actual candidate images exclude the genuine positive Omega element. -/
theorem generatedFifthRootEight_tensor_candidate_images_exclude_Omega (b : ZMod 2) (j : Fin 16) :
    generatedTenthQWordImage 8 7 (generatedFifthQCandidate b j) ≠ sourceOmegaQ := by
  intro he
  rw [generatedTenth_Q_word_fast 8 generatedAxisGlobalFifthQCache08_actual] at he
  apply generatedFifthRootEight_tensor_candidate_image_coordinates b j
  rw [he]
  exact fun _ => rfl

/-- The same actual quotient exclusion also excludes the genuine negative Omega element. -/
theorem generatedFifthRootEight_tensor_candidate_images_exclude_antiOmega
    (b : ZMod 2) (j : Fin 16) :
    generatedTenthQWordImage 8 7 (generatedFifthQCandidate b j) ≠
      generatedTenthTensorAntiOmega := by
  intro he
  rw [generatedTenth_Q_word_fast 8 generatedAxisGlobalFifthQCache08_actual] at he
  apply generatedFifthRootEight_tensor_candidate_image_coordinates b j
  have hb : generatedTenthTensorAntiOmega.base = sourceOmegaQ.base := by
    change (qCentral 1 * sourceOmegaQ).base = sourceOmegaQ.base
    exact qCentral_mul_base 1 sourceOmegaQ
  rw [he, hb]
  exact fun _ => rfl

/-- The original root-eight triality image has a genuinely nonzero odd short coefficient. -/
theorem generatedFifthRootEight_odd_short_exists_nonzero :
    ∃ d : Fin 2048, ∃ i : Fin 24,
      (griessConwayEncode generatedFifthRootEightAxis).2.1 (Sum.inr (Sum.inr (d, i))) ≠ 0 := by
  rw [generatedFifthRootEightAxis_local_expression, generatedFifthRootEightLocal]
  exact generatedTenth_odd_nonzero_of_candidate_images 8
    generatedFifthRootEight_tensor_candidate_images_exclude_antiOmega

/-- The complete actual root-eight outgoing tensor is genuinely nonzero. -/
theorem generatedFifthRootEight_outgoing_tensor_ne_zero :
    (griessConwayEncode generatedFifthRootEightAxis).2.2 ≠ 0 := by
  rw [generatedFifthRootEightAxis_local_expression, generatedFifthRootEightLocal]
  exact generatedTenth_tensor_nonzero_of_candidate_images 8
    generatedFifthRootEight_tensor_candidate_images_exclude_Omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
