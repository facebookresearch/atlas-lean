/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR83nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (matrix) of the identification Root8[11]- <-> Twelfth[29]- (record r8f:R83-, e
= -1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR83n_hm : triMatF false wR8fR83nL wR8fR83nW = selfMatQ wR8fR83nW := by
  rw [triMatF_eq_ZI false wR8fR83nL wR8fR83nW (srcRootEightMatZc.act wR8fR83nH)
      (twelfthSrcMatZ.act wR8fR83nG)
    (srcRootEightMat_act_entryZc wR8fR83nH) (twelfthSrcMat_act_entryZ wR8fR83nG),
    selfMatQ_eq_ZI wR8fR83nW (twelfthSrcMatZ.act wR8fR83nG) (twelfthSrcMat_act_entryZ wR8fR83nG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
