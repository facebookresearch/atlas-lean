/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightMateTensorCoordinates

/-! Complete bounded original integer mate tensor checks. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000 in
/-- All original tensor coordinates in this bounded subblock satisfy the genuine mate equation. -/
theorem generatedRootEight_mate_tensor_cache_block_02_00 : ∀ u : Fin 64, ∀ i : Fin 24,
    generatedRootEightMateTensorCacheCondition ⟨512 + u.val, by omega⟩ i := by
  unfold generatedRootEightMateTensorCacheCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
