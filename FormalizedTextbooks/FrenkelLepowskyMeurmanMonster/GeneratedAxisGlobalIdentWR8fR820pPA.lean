/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR820pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentSrcRootEightCF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (octad check, matrix, pairs) of the identification Fourth[10]+ <-> Root8[25]+
(record r8f:R820+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR820p_hm : triMatF true wR8fR820pL wR8fR820pW = selfMatQ wR8fR820pW := by
  rw [triMatF_eq_ZI true wR8fR820pL wR8fR820pW (srcRootEightMatZ.act wR8fR820pH)
      (fourthSrcMatZ.act wR8fR820pG)
    (srcRootEightMat_act_entryZ wR8fR820pH) (fourthSrcMat_act_entryZ wR8fR820pG),
    selfMatQ_eq_ZI wR8fR820pW (fourthSrcMatZ.act wR8fR820pG) (fourthSrcMat_act_entryZ wR8fR820pG)]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair part equals the pair self part of the target. -/
theorem wR8fR820p_hp : pairSumQ true wR8fR820pL wR8fR820pW = wR8fR820pW.sden * (selfPairsZ
    wR8fR820pW : ℚ) := by
  rw [pairSumQ_eq_ZI true wR8fR820pL wR8fR820pW (srcRootEightMatZ.act wR8fR820pH)
      (srcRootEightMat_act_entryZ wR8fR820pH)]
  decide +kernel

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
