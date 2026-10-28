/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber2Data

/-! Kernel-checked descent blocks 4 to 7 of the octad binary forest on the fiber over the dual
value 2. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 4 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber2Block04 :
    generatedAxisGlobalTwelveOctadFiber2Loop 16384 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 5 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber2Block05 :
    generatedAxisGlobalTwelveOctadFiber2Loop 20480 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 6 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber2Block06 :
    generatedAxisGlobalTwelveOctadFiber2Loop 24576 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 7 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber2Block07 :
    generatedAxisGlobalTwelveOctadFiber2Loop 28672 4096 = true := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
