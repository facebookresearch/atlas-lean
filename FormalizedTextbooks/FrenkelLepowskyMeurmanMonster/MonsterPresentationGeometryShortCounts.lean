/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite character counts from the original twelve Golay generators. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessCoordinates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

set_option maxRecDepth 100000 in
set_option maxHeartbeats 40000000 in
-- Count the genuine weight-eight labels among all 4096 encoded codewords.
/-- Exactly 407 original octads agree at the first two physical positions. -/
theorem monsterGeometryShort_octads_agree_card :
    (golayOctads.filter (fun d =>
      (golayEncodedMask d.val).testBit 0 = (golayEncodedMask d.val).testBit 1)).card = 407 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
-- Count the 2048 original odd-family labels without evaluating their 24 positions.
/-- Half of the original low eleven-bit code labels agree at these two physical positions. -/
theorem monsterGeometryShort_odd_agree_card :
    (Finset.univ.filter (fun d : Fin 2048 =>
      (golayEncodedMask d.val).testBit 0 = (golayEncodedMask d.val).testBit 1)).card = 1024 := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
