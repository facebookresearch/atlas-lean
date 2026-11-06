/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthSpreadOrbitBoundedCertificates

/-! Finite acyclic edge, distinctness and fingerprint checks for nine existing actual frame-system
indices. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 20000000 in
-- Check only 960 stated index rows.
/-- Each row contains nine distinct existing frame-system indices. -/
theorem generatedNinth_spread_indices_injective : ∀ i : Fin 960,
    Function.Injective (generatedNinthSpreadIndices i) :=
  generatedNinth_spread_bounded_indices_injective

set_option maxHeartbeats 20000000 in
-- Exact sums retain every one of the nine displayed indices.
/-- The compact residue equals the complete nine-system incidence sum. -/
theorem generatedNinth_spread_hash_sum : ∀ i : Fin 960,
    (∑ j : Fin 9, 2 ^ (generatedNinthSpreadIndices i j).val) % 18446744073709551557 =
      generatedNinthSpreadHashes i :=
  generatedNinth_spread_bounded_hash_sum

set_option maxHeartbeats 20000000 in
-- Verify 960 balanced retrieval equations.
/-- The exact residue lookup recovers every chronological orbit index. -/
theorem generatedNinth_spread_lookup : ∀ i : Fin 960,
    generatedNinthSpreadLookup (generatedNinthSpreadHashes i) = i.val :=
  generatedNinth_spread_bounded_lookup

set_option maxHeartbeats 20000000 in
-- The initial row is handled separately in the genuine word induction.
/-- Every noninitial parent is earlier in the original finite tree. -/
theorem generatedNinth_spread_parent_lt : ∀ i : Fin 960, i ≠ 0 →
    (generatedNinthSpreadParent i).val < i.val :=
  generatedNinth_spread_bounded_parent_lt

set_option maxHeartbeats 20000000 in
-- Each parent letter acts on all nine original indices.
/-- Every proposed edge has the exact full system-index images stated by its source table. -/
theorem generatedNinth_spread_edge_indices : ∀ i : Fin 960, i ≠ 0 → ∀ j : Fin 9,
    generatedNinthSpreadSystemTarget (generatedNinthSpreadGenerator i)
      (generatedNinthSpreadIndices (generatedNinthSpreadParent i) j) =
        generatedNinthSpreadIndices i (generatedNinthSpreadEdgePermutation i j) :=
  generatedNinth_spread_bounded_edge_indices

set_option maxHeartbeats 20000000 in
-- Check the finite nine-entry reordering in every edge.
/-- Every edge reordering covers the entire child row. -/
theorem generatedNinth_spread_edge_permutation_surjective : ∀ i : Fin 960,
    Function.Surjective (generatedNinthSpreadEdgePermutation i) :=
  generatedNinth_spread_bounded_edge_permutation_surjective

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
