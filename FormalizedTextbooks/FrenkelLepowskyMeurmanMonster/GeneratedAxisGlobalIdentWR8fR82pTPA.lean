/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR82pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[18]- <-> Root8[2]+
(record r8f:R82+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wR8fR82pT_LME : ∀ i j, wR8fR82pTL.mat.entry i j = (srcRootEightMatZc.actT
    wR8fR82pTHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR82pTHPlan_word]
  exact srcRootEightMat_act_entryZc wR8fR82pTH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wR8fR82pT_WME : ∀ i j, wR8fR82pTW.mat.entry i j = (eighthSrcMatZ.actT
    wR8fR82pTGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR82pTGPlan_word]
  exact eighthSrcMat_act_entryZ wR8fR82pTG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR82pT_hm : triMatF true wR8fR82pTL wR8fR82pTW = selfMatQ wR8fR82pTW := by
  rw [triMatF_eq_ZI true wR8fR82pTL wR8fR82pTW (srcRootEightMatZc.actT wR8fR82pTHPlan)
      (eighthSrcMatZ.actT wR8fR82pTGPlan)
    wR8fR82pT_LME wR8fR82pT_WME,
    selfMatQ_eq_ZI wR8fR82pTW (eighthSrcMatZ.actT wR8fR82pTGPlan) wR8fR82pT_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wR8fR82pT_pd : labDistinct wR8fR82pTW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wR8fR82pT_hpc : pairChk true (srcRootEightMatZc.actT wR8fR82pTHPlan) wR8fR82pTL wR8fR82pTW
    (wR8fR82pTW.sden * (sqSumZ wR8fR82pTW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR82pT_hp : pairSumQ true wR8fR82pTL wR8fR82pTW = wR8fR82pTW.sden * (selfPairsZ
    wR8fR82pTW : ℚ) := by
  rw [selfPairsZ_of_distinct wR8fR82pTW wR8fR82pT_pd]
  exact pairSumQ_of_chk true wR8fR82pTL wR8fR82pTW (srcRootEightMatZc.actT wR8fR82pTHPlan)
      wR8fR82pT_LME wR8fR82pT_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
