/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pwChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (matrix) of the identification Root8[22]+ <-> Root8[22]+ (record r8f:R816+, e
= 1)

Dense pair blocks: the pair part of the pairing is evaluated in parts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false


set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR816pw_hm : triMatF true wR8fR816pwL wR8fR816pwW = selfMatQ wR8fR816pwW := by
  rw [triMatF_eq_ZI true wR8fR816pwL wR8fR816pwW (srcRootEightMatZc.act wR8fR816pwH)
      (srcRootEightMatZc.act wR8fR816pwG)
    (srcRootEightMat_act_entryZc wR8fR816pwH) (srcRootEightMat_act_entryZc wR8fR816pwG),
    selfMatQ_eq_ZI wR8fR816pwW (srcRootEightMatZc.act wR8fR816pwG) (srcRootEightMat_act_entryZc
        wR8fR816pwG)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
