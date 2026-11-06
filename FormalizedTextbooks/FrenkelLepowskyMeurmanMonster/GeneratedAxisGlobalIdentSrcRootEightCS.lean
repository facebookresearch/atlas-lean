/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEight
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW

/-! # Compact checkpoints of the incoming Root8 tensor

The kernel checks that each part of the Root8 source word maps the widened previous checkpoint
(first the Fifth tensor) to the next compact literal, by one packed comparison per column
(`twColCheck`, worker gtwelfth) at a small field width. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word in its parts (the head part acts last). -/
theorem srcRootEightYWord_parts : srcRootEightYWord = srcRootEightCW2 ++ (srcRootEightCW1 ++
    srcRootEightCW0) := by
  rfl

set_option maxRecDepth 100000 in
/-- Denominators and growth factors of the parts. -/
theorem srcRootEightC_dens :
    tensorWordDenAll srcRootEightCW0 = 32 ∧
      tensorWordGrowthAll srcRootEightCW0 = 2048 ∧
      tensorWordDenAll srcRootEightCW1 = 32 ∧
      tensorWordGrowthAll srcRootEightCW1 = 2048 ∧
      tensorWordDenAll srcRootEightCW2 = 64 ∧
      tensorWordGrowthAll srcRootEightCW2 = 16384 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `0` of the source word maps the Fifth tensor to `srcRootEightCL0`. -/
theorem srcRootEightC_check0 :
    twColCheck 20 2 4 (tensorWordAll 20 srcRootEightCW0
      (fifthSrcXW 20)) srcRootEightCL0 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `1` of the source word maps the widened checkpoint `srcRootEightCL0` to
`srcRootEightCL1`. -/
theorem srcRootEightC_check1 :
    twColCheck 16 2 32 (tensorWordAll 16 srcRootEightCW1
      (twWidenT 2 16 srcRootEightCL0)) srcRootEightCL1 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `2` of the source word maps the widened checkpoint `srcRootEightCL1` to
`srcRootEightCYLit`. -/
theorem srcRootEightC_check2 :
    twColCheck 16 4 8 (tensorWordAll 16 srcRootEightCW2
      (twWidenT 2 16 srcRootEightCL1)) srcRootEightCYLit = true := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
