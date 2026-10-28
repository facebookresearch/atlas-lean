/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenthCData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcTenth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW

/-! # Compact checkpoints of the incoming Tenth tensor

The kernel checks that each part of the Tenth source word maps the widened previous checkpoint
(first the Fifth tensor) to the next compact literal, by one packed comparison per column
(`twColCheck`, worker gtwelfth) at a small field width. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word in its parts (the head part acts last). -/
theorem srcTenthYWord_parts : srcTenthYWord = srcTenthCW3 ++ (srcTenthCW2 ++ (srcTenthCW1 ++
    srcTenthCW0)) := by
  rfl

set_option maxRecDepth 100000 in
/-- Denominators and growth factors of the parts. -/
theorem srcTenthC_dens :
    tensorWordDenAll srcTenthCW0 = 256 ∧
      tensorWordGrowthAll srcTenthCW0 = 65536 ∧
      tensorWordDenAll srcTenthCW1 = 32 ∧
      tensorWordGrowthAll srcTenthCW1 = 2048 ∧
      tensorWordDenAll srcTenthCW2 = 32 ∧
      tensorWordGrowthAll srcTenthCW2 = 2048 ∧
      tensorWordDenAll srcTenthCW3 = 64 ∧
      tensorWordGrowthAll srcTenthCW3 = 16384 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `0` of the source word maps the Fifth tensor to `srcTenthCL0`. -/
theorem srcTenthC_check0 :
    twColCheck 24 2 32 (tensorWordAll 24 srcTenthCW0
      (fifthSrcXW 24)) srcTenthCL0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `1` of the source word maps the widened checkpoint `srcTenthCL0` to `srcTenthCL1`. -/
theorem srcTenthC_check1 :
    twColCheck 16 3 8 (tensorWordAll 16 srcTenthCW1
      (twWidenT 2 16 srcTenthCL0)) srcTenthCL1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `2` of the source word maps the widened checkpoint `srcTenthCL1` to `srcTenthCL2`. -/
theorem srcTenthC_check2 :
    twColCheck 16 4 32 (tensorWordAll 16 srcTenthCW2
      (twWidenT 3 16 srcTenthCL1)) srcTenthCL2 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `3` of the source word maps the widened checkpoint `srcTenthCL2` to `srcTenthCYLit`. -/
theorem srcTenthC_check3 :
    twColCheck 20 4 32 (tensorWordAll 20 srcTenthCW3
      (twWidenT 4 20 srcTenthCL2)) srcTenthCYLit = true := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
