/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR816pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM

/-! # Factory parts (octad check, matrix, pairs) of the identification Root8[22]+ <-> Root8[22]+
(record r8f:R816+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wR8fR816pT_LME : ∀ i j, wR8fR816pTL.mat.entry i j = (srcRootEightMatZc.actT
    wR8fR816pTHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR816pTHPlan_word]
  exact srcRootEightMat_act_entryZc wR8fR816pTH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wR8fR816pT_WME : ∀ i j, wR8fR816pTW.mat.entry i j = (srcRootEightMatZc.actT
    wR8fR816pTGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR816pTGPlan_word]
  exact srcRootEightMat_act_entryZc wR8fR816pTG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR816pT_hm : triMatF true wR8fR816pTL wR8fR816pTW = selfMatQ wR8fR816pTW := by
  rw [triMatF_eq_ZI true wR8fR816pTL wR8fR816pTW (srcRootEightMatZc.actT wR8fR816pTHPlan)
      (srcRootEightMatZc.actT wR8fR816pTGPlan)
    wR8fR816pT_LME wR8fR816pT_WME,
    selfMatQ_eq_ZI wR8fR816pTW (srcRootEightMatZc.actT wR8fR816pTGPlan) wR8fR816pT_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wR8fR816pT_pd : labDistinct wR8fR816pTW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wR8fR816pT_hpc : pairChk true (srcRootEightMatZc.actT wR8fR816pTHPlan) wR8fR816pTL
    wR8fR816pTW (wR8fR816pTW.sden * (sqSumZ wR8fR816pTW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR816pT_hp : pairSumQ true wR8fR816pTL wR8fR816pTW = wR8fR816pTW.sden * (selfPairsZ
    wR8fR816pTW : ℚ) := by
  rw [selfPairsZ_of_distinct wR8fR816pTW wR8fR816pT_pd]
  exact pairSumQ_of_chk true wR8fR816pTL wR8fR816pTW (srcRootEightMatZc.actT wR8fR816pTHPlan)
      wR8fR816pT_LME wR8fR816pT_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
