/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR817pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF

/-! # Factory parts (octad check, matrix, pairs) of the identification Root8[26]+ <-> Root8[26]+
(record r8f:R817+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR817p_hm : triMatF true wR8fR817pL wR8fR817pW = selfMatQ wR8fR817pW := by
  rw [triMatF_eq_ZI true wR8fR817pL wR8fR817pW (srcRootEightMatZ.act wR8fR817pH)
      (srcRootEightMatZ.act wR8fR817pG)
    (srcRootEightMat_act_entryZ wR8fR817pH) (srcRootEightMat_act_entryZ wR8fR817pG),
    selfMatQ_eq_ZI wR8fR817pW (srcRootEightMatZ.act wR8fR817pG) (srcRootEightMat_act_entryZ
        wR8fR817pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wR8fR817p_hp : pairSumQ true wR8fR817pL wR8fR817pW = wR8fR817pW.sden * (selfPairsZ
    wR8fR817pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wR8fR817pL wR8fR817pW (srcRootEightMatZ.act wR8fR817pH)
      (srcRootEightMat_act_entryZ wR8fR817pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
