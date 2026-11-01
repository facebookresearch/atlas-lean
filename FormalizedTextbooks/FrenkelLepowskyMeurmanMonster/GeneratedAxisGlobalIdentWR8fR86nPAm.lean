/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (matrix) of the identification Root8[12]- <-> Twelfth[34]- (record r8f:R86-, e
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
theorem wR8fR86n_hm : triMatF false wR8fR86nL wR8fR86nW = selfMatQ wR8fR86nW := by
  rw [triMatF_eq_ZI false wR8fR86nL wR8fR86nW (srcRootEightMatZc.act wR8fR86nH)
      (twelfthSrcMatZ.act wR8fR86nG)
    (srcRootEightMat_act_entryZc wR8fR86nH) (twelfthSrcMat_act_entryZ wR8fR86nG),
    selfMatQ_eq_ZI wR8fR86nW (twelfthSrcMatZ.act wR8fR86nG) (twelfthSrcMat_act_entryZ wR8fR86nG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
