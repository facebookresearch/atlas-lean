/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialTensorCachedData

/-! A bounded original full tensor check using complete affine-address and sign caches. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Check every ordinary coordinate for sixty-four original spin labels with full signs retained.
/-- Every original coordinate in this bounded complete signed tensor sample agrees. -/
theorem generatedSixth_monomial_tensor_cached_sample : ∀ n : Fin 64, ∀ i : Fin 24,
    generatedSixthMonomialTensorCached 0 ⟨n.val, by omega⟩ i =
      generatedSixthTensorExecutable ⟨n.val, by omega⟩ i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
