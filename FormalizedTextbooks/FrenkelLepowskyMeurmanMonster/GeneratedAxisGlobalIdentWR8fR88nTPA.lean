/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR88nTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Root8[20]- <-> Tenth[69]+
(record r8f:R88-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wR8fR88nT_LME : ∀ i j, wR8fR88nTL.mat.entry i j = (srcRootEightMatZc.actT
    wR8fR88nTHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR88nTHPlan_word]
  exact srcRootEightMat_act_entryZc wR8fR88nTH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wR8fR88nT_WME : ∀ i j, wR8fR88nTW.mat.entry i j = (srcTenthMatZc.actT
    wR8fR88nTGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR88nTGPlan_word]
  exact srcTenthMat_act_entryZc wR8fR88nTG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR88nT_hm : triMatF false wR8fR88nTL wR8fR88nTW = selfMatQ wR8fR88nTW := by
  rw [triMatF_eq_ZI false wR8fR88nTL wR8fR88nTW (srcRootEightMatZc.actT wR8fR88nTHPlan)
      (srcTenthMatZc.actT wR8fR88nTGPlan)
    wR8fR88nT_LME wR8fR88nT_WME,
    selfMatQ_eq_ZI wR8fR88nTW (srcTenthMatZc.actT wR8fR88nTGPlan) wR8fR88nT_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wR8fR88nT_pd : labDistinct wR8fR88nTW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wR8fR88nT_hpc : pairChk false (srcRootEightMatZc.actT wR8fR88nTHPlan) wR8fR88nTL
    wR8fR88nTW (wR8fR88nTW.sden * (sqSumZ wR8fR88nTW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR88nT_hp : pairSumQ false wR8fR88nTL wR8fR88nTW = wR8fR88nTW.sden * (selfPairsZ
    wR8fR88nTW : ℚ) := by
  rw [selfPairsZ_of_distinct wR8fR88nTW wR8fR88nT_pd]
  exact pairSumQ_of_chk false wR8fR88nTL wR8fR88nTW (srcRootEightMatZc.actT wR8fR88nTHPlan)
      wR8fR88nT_LME wR8fR88nT_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
