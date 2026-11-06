/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OrbitEdgesData

/-! Complete original integer source images for incoming root-orbit packet 3. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option maxRecDepth 100000

/-- Every valid noninitial original address retains all twenty-four source coordinates. -/
theorem generatedTenth_e7_orbit_edges_packet_03 : ∀ u : Fin 8,
    if hn : 3 * 8 + u.val < 63 then
      if _hi : (⟨3 * 8 + u.val, hn⟩ : Fin 63) ≠ 0 then
        generatedTenthE7OrbitEdgeCondition ⟨3 * 8 + u.val, hn⟩ else True else True := by
  unfold generatedTenthE7OrbitEdgeCondition
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
