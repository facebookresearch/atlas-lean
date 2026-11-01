/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceCacheData

/-! Bounded complete source spin cache certificate at labels 1024 through 2047. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

set_option maxHeartbeats 32000000 in
-- Check every signed coefficient at all eight columns and all 1024 labels in this packet.
/-- All original source labels in the packet equal the signed literal source cache. -/
theorem generatedRootEight_incoming_tensor_source_cache_packet01 :
    ∀ r : Fin 8, ∀ k : Fin 1024,
      generatedTwelfthTensorSourceSpinSmall r ⟨1024 + k.val, by omega⟩ =
        generatedRootEightIncomingTensorSourceCache r ⟨1024 + k.val, by omega⟩ := by
  have h : ∀ r : Fin 8, ∀ k : Fin 1024,
      generatedTwelfthTensorSourceInitialSparseSpin r ⟨1024 + k.val, by omega⟩ =
        generatedRootEightIncomingTensorSourceCache r ⟨1024 + k.val, by omega⟩ := by
    decide +kernel
  intro r k
  exact (generatedTwelfth_tensor_source_spin_fast_actual r _).trans
    ((generatedTwelfth_tensor_source_initial_sparse_actual r _).trans (h r k))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
