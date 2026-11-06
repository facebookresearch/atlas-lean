/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR811nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octad check, matrix, pairs) of the identification Root8[13]- <-> Root8[13]-
(record r8f:R811-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR811nT_hm : triMatF false wR8fR811nTL wR8fR811nTW = selfMatQ wR8fR811nTW := by
  rw [triMatF_eq_ZI false wR8fR811nTL wR8fR811nTW (srcRootEightMatZc.act wR8fR811nTH)
      (srcRootEightMatZc.act wR8fR811nTG)
    (srcRootEightMat_act_entryZc wR8fR811nTH) (srcRootEightMat_act_entryZc wR8fR811nTG),
    selfMatQ_eq_ZI wR8fR811nTW (srcRootEightMatZc.act wR8fR811nTG) (srcRootEightMat_act_entryZc
        wR8fR811nTG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wR8fR811nT_hp : pairSumQ false wR8fR811nTL wR8fR811nTW = wR8fR811nTW.sden * (selfPairsZ
    wR8fR811nTW : ℚ) := by
  rw [pairSumQ_eq_ZI false wR8fR811nTL wR8fR811nTW (srcRootEightMatZc.act wR8fR811nTH)
      (srcRootEightMat_act_entryZc wR8fR811nTH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
