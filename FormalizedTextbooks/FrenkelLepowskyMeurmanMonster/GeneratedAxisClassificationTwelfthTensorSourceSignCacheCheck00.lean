/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthTensorSourceSignCacheData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
/-- Every actual source phase is checked, retaining the full high-bit and physical corrections. -/
theorem generatedTwelfth_tensor_source_sign_cache_check00 : ∀ e : Fin 2048,
    generatedAxisGlobalIntSign (golayLabelCoefficients (generatedTwelfthTensorSourceSignCode 0) 11) *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
          (generatedTwelfthTensorSourceSignCode 0) 0
          (generatedAxisGlobalSignInputCode (generatedTwelfthTensorSourceSignCode 0) e) e) =
      generatedTwelfthTensorSourceSignPhase 0 0 e ∧
    generatedTwelfthTensorPhysicalSign (generatedTwelfthTensorSourceSignCode 0) 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
          (generatedTwelfthTensorSourceSignCode 0) e 0) =
      generatedTwelfthTensorSourceSignPhase 0 1 e := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
