/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTwelfthS

/-! # Factory parts (matrix) of the identification Root8[16]+ <-> Twelfth[24]+ (record r8f:R81+, e
= 1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR81p_hm : triMatF true wR8fR81pL wR8fR81pW = selfMatQ wR8fR81pW := by
  rw [triMatF_eq_ZI true wR8fR81pL wR8fR81pW (srcRootEightMatZc.act wR8fR81pH) (twelfthSrcMatZ.act
      wR8fR81pG)
    (srcRootEightMat_act_entryZc wR8fR81pH) (twelfthSrcMat_act_entryZ wR8fR81pG),
    selfMatQ_eq_ZI wR8fR81pW (twelfthSrcMatZ.act wR8fR81pG) (twelfthSrcMat_act_entryZ wR8fR81pG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
