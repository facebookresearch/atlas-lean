/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitLookup

/-! All original spread checks, partitioned into thirty disjoint 32-index packets. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 20000000 in
-- Check all 32 original orbit indices in this packet, retaining the full predicate.
/-- Exact original spread condition on this complete 32-index packet. -/
theorem generatedNinth_spread_bounded_indices_injective_packet_20 : ∀ m : Fin 32,
    let i : Fin 960 := ⟨640 + m.val, by omega⟩
    Function.Injective (generatedNinthSpreadIndices i) := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all 32 original orbit indices in this packet, retaining the full predicate.
/-- Exact original spread condition on this complete 32-index packet. -/
theorem generatedNinth_spread_bounded_hash_sum_packet_20 : ∀ m : Fin 32,
    let i : Fin 960 := ⟨640 + m.val, by omega⟩
    (∑ j : Fin 9, 2 ^ (generatedNinthSpreadIndices i j).val) % 18446744073709551557 =
      generatedNinthSpreadHashes i := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all 32 original orbit indices in this packet, retaining the full predicate.
/-- Exact original spread condition on this complete 32-index packet. -/
theorem generatedNinth_spread_bounded_lookup_packet_20 : ∀ m : Fin 32,
    let i : Fin 960 := ⟨640 + m.val, by omega⟩
    generatedNinthSpreadLookup (generatedNinthSpreadHashes i) = i.val := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all 32 original orbit indices in this packet, retaining the full predicate.
/-- Exact original spread condition on this complete 32-index packet. -/
theorem generatedNinth_spread_bounded_parent_lt_packet_20 : ∀ m : Fin 32,
    let i : Fin 960 := ⟨640 + m.val, by omega⟩
    i ≠ 0 →
    (generatedNinthSpreadParent i).val < i.val := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all 32 original orbit indices in this packet, retaining the full predicate.
/-- Exact original spread condition on this complete 32-index packet. -/
theorem generatedNinth_spread_bounded_edge_indices_packet_20 : ∀ m : Fin 32,
    let i : Fin 960 := ⟨640 + m.val, by omega⟩
    i ≠ 0 → ∀ j : Fin 9,
    generatedNinthSpreadSystemTarget (generatedNinthSpreadGenerator i)
      (generatedNinthSpreadIndices (generatedNinthSpreadParent i) j) =
        generatedNinthSpreadIndices i (generatedNinthSpreadEdgePermutation i j) := by
  decide +kernel

set_option maxHeartbeats 20000000 in
-- Check all 32 original orbit indices in this packet, retaining the full predicate.
/-- Exact original spread condition on this complete 32-index packet. -/
theorem generatedNinth_spread_bounded_edge_permutation_surjective_packet_20 : ∀ m : Fin 32,
    let i : Fin 960 := ⟨640 + m.val, by omega⟩
    Function.Surjective (generatedNinthSpreadEdgePermutation i) := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
