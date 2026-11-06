/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingTensorSourceCacheData

/-! Bounded complete source spin cache certificate at labels 3072 through 4095. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 0 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column0 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 0 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 0 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 1 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column1 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 1 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 1 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 2 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column2 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 2 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 2 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 3 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column3 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 3 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 3 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 4 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column4 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 4 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 4 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 5 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column5 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 5 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 5 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 6 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column6 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 6 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 6 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

set_option maxHeartbeats 8000000 in
-- Keep one original source column in each kernel certificate to release finite memoization.
/-- Every original label in column 7 of the last packet retains its entire signed coefficient. -/
private theorem source_cache_column7 : ∀ k : Fin 1024,
    generatedTwelfthTensorSourceInitialSparseSpin 7 ⟨3072 + k.val, by omega⟩ =
      generatedRootEightIncomingTensorSourceCache 7 ⟨3072 + k.val, by omega⟩ := by
  decide +kernel

/-- All original source labels in the packet equal the signed literal source cache. -/
theorem generatedRootEight_incoming_tensor_source_cache_packet03 :
    ∀ r : Fin 8, ∀ k : Fin 1024,
      generatedTwelfthTensorSourceSpinSmall r ⟨3072 + k.val, by omega⟩ =
        generatedRootEightIncomingTensorSourceCache r ⟨3072 + k.val, by omega⟩ := by
  intro r k
  apply (generatedTwelfth_tensor_source_spin_fast_actual r _).trans
  apply (generatedTwelfth_tensor_source_initial_sparse_actual r _).trans
  fin_cases r
  · exact source_cache_column0 k
  · exact source_cache_column1 k
  · exact source_cache_column2 k
  · exact source_cache_column3 k
  · exact source_cache_column4 k
  · exact source_cache_column5 k
  · exact source_cache_column6 k
  · exact source_cache_column7 k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
