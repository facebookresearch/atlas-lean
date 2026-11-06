/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadFiber1Data

/-! Kernel-checked descent blocks 12 to 15 of the octad binary forest on the fiber over the dual
value 1. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxRecDepth 20000

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 12 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block12 :
    generatedAxisGlobalTwelveOctadFiber1Loop 49152 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 13 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block13 :
    generatedAxisGlobalTwelveOctadFiber1Loop 53248 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 14 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block14 :
    generatedAxisGlobalTwelveOctadFiber1Loop 57344 4096 = true := by
  decide +kernel

set_option maxHeartbeats 400000000 in
-- Check all 4096 fiber points of one block.
/-- Every point of fiber block 15 is a root or descends. -/
theorem generatedAxisGlobalTwelveOctadFiber1Block15 :
    generatedAxisGlobalTwelveOctadFiber1Loop 61440 4096 = true := by
  decide +kernel


end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
