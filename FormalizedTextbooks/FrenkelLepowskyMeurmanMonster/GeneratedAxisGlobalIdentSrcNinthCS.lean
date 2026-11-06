/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcNinthCData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcNinth
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentFifthSourceW

/-! # Compact checkpoints of the incoming Ninth tensor

The kernel checks that each part of the Ninth source word maps the widened previous checkpoint
(first the Fifth tensor) to the next compact literal, by one packed comparison per column
(`twColCheck`, worker gtwelfth) at a small field width. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The source word in its parts (the head part acts last). -/
theorem srcNinthYWord_parts : srcNinthYWord = srcNinthCW0 := by
  rfl

set_option maxRecDepth 100000 in
/-- Denominators and growth factors of the parts. -/
theorem srcNinthC_dens :
    tensorWordDenAll srcNinthCW0 = 65536 ∧
      tensorWordGrowthAll srcNinthCW0 = 4294967296 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- Part `0` of the source word maps the Fifth tensor to `srcNinthCYLit`. -/
theorem srcNinthC_check0 :
    twColCheck 40 4 1024 (tensorWordAll 40 srcNinthCW0
      (fifthSrcXW 40)) srcNinthCYLit = true := by
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
