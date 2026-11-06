/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber1Data

/-! Kernel-checked descent blocks 8 to 11 of the octad binary forest on the fiber over the dual
value 1. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 8 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block08 :
    generatedAxisGlobalTwelveOctadFiber1Loop 32768 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 9 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block09 :
    generatedAxisGlobalTwelveOctadFiber1Loop 36864 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 10 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block10 :
    generatedAxisGlobalTwelveOctadFiber1Loop 40960 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 11 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block11 :
    generatedAxisGlobalTwelveOctadFiber1Loop 45056 4096 = true := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
