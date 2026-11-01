/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (matrix) of the identification Root8[4]- <-> Root8[4]- (record r8f:R822-, e =
-1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR822n_hm : triMatF false wR8fR822nL wR8fR822nW = selfMatQ wR8fR822nW := by
  rw [triMatF_eq_ZI false wR8fR822nL wR8fR822nW (srcRootEightMatZc.act wR8fR822nH)
      (srcRootEightMatZc.act wR8fR822nG)
    (srcRootEightMat_act_entryZc wR8fR822nH) (srcRootEightMat_act_entryZc wR8fR822nG),
    selfMatQ_eq_ZI wR8fR822nW (srcRootEightMatZc.act wR8fR822nG) (srcRootEightMat_act_entryZc
        wR8fR822nG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
