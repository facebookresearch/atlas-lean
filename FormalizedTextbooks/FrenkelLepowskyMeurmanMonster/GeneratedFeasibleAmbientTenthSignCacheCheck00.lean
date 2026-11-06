/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleAmbientTenthSignCacheData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
-- All 2048 low dictionary labels are checked.
/-- Every source phase of root-two code 0 is checked. -/
theorem generatedFeasibleAmbientTenth_sign_cache_check00 : ∀ e : Fin 2048,
    generatedAxisGlobalIntSign (golayLabelCoefficients (generatedFeasibleAmbientTenthSignCode 0)
        11) *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignYPhase
          (generatedFeasibleAmbientTenthSignCode 0) 0
          (generatedAxisGlobalSignInputCode (generatedFeasibleAmbientTenthSignCode 0) e) e) =
      generatedFeasibleAmbientTenthSignPhase 0 0 e ∧
    generatedTwelfthTensorPhysicalSign (generatedFeasibleAmbientTenthSignCode 0) 0 *
        generatedAxisGlobalIntSign (generatedAxisGlobalSignZPhase
          (generatedFeasibleAmbientTenthSignCode 0) e 0) =
      generatedFeasibleAmbientTenthSignPhase 0 1 e := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
