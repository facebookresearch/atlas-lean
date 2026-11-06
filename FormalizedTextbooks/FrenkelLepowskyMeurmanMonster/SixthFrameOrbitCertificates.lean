/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SixthFrameOrbitDataLookup

/-! Exact finite packed-value checks, before any source generator or orbit interpretation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The initial catalogue value is the original Omega coordinate mask. -/
theorem sixthFrameOrbit_initial : sixthFrameOrbitPoints 0 = 2048 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The finite balanced tree checks 891 retrieval equations.
/-- The literal catalogue lookup recovers every original chronological index. -/
theorem sixthFrameOrbit_lookup : ∀ i : Fin 891,
    sixthFrameOrbitLookup (sixthFrameOrbitPoints i) = i.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Verify 891 bounds on the actual packed values.
/-- Every proposed value lies within the genuine 24-bit binary coordinate range. -/
theorem sixthFrameOrbit_point_bounds : ∀ i : Fin 891, sixthFrameOrbitPoints i < 2 ^ 24 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The original chronological parent relation is checked on its 890 noninitial entries.
/-- Every noninitial parent is strictly earlier; the eventual orbit proof is acyclic. -/
theorem sixthFrameOrbit_parent_before : ∀ i : Fin 891,
    i ≠ 0 → (sixthFrameOrbitParent i).val < i.val := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 12000000 in
-- Check all 890 original packed-column edge equations by exact XOR arithmetic.
/-- Every recorded parent transition is the literal action of its entire packed column matrix. -/
theorem sixthFrameOrbit_edge_check : ∀ i : Fin 891, i ≠ 0 →
    sixthFrameOrbitMaskApply (sixthFrameOrbitColumns (sixthFrameOrbitGenerator i))
      (sixthFrameOrbitPoints (sixthFrameOrbitParent i)) = sixthFrameOrbitPoints i := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
