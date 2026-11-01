/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber1Data

/-! Kernel-checked descent blocks 0 to 3 of the octad binary forest on the fiber over the dual
value 1. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 0 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block00 :
    generatedAxisGlobalTwelveOctadFiber1Loop 0 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 1 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block01 :
    generatedAxisGlobalTwelveOctadFiber1Loop 4096 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 2 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block02 :
    generatedAxisGlobalTwelveOctadFiber1Loop 8192 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 3 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block03 :
    generatedAxisGlobalTwelveOctadFiber1Loop 12288 4096 = true := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
