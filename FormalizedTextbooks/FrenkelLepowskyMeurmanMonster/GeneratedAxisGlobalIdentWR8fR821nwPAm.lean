/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR821nwChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (matrix) of the identification Root8[33]- <-> Root8[33]- (record r8f:R821-, e
= -1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR821nw_hm : triMatF false wR8fR821nwL wR8fR821nwW = selfMatQ wR8fR821nwW := by
  rw [triMatF_eq_ZI false wR8fR821nwL wR8fR821nwW (srcRootEightMatZc.act wR8fR821nwH)
      (srcRootEightMatZc.act wR8fR821nwG)
    (srcRootEightMat_act_entryZc wR8fR821nwH) (srcRootEightMat_act_entryZc wR8fR821nwG),
    selfMatQ_eq_ZI wR8fR821nwW (srcRootEightMatZc.act wR8fR821nwG) (srcRootEightMat_act_entryZc
        wR8fR821nwG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
