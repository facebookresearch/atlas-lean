/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE33T32pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[46]+ <-> Tenth[46]+
(record goctad:E33@T32+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGoctadE33T32p_LME : ∀ i j, wGoctadE33T32pL.mat.entry i j = (eighthSrcMatZ.actT
    wGoctadE33T32pHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE33T32pHPlan_word]
  exact eighthSrcMat_act_entryZ wGoctadE33T32pH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGoctadE33T32p_WME : ∀ i j, wGoctadE33T32pW.mat.entry i j = (srcTenthMatZc.actT
    wGoctadE33T32pGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE33T32pGPlan_word]
  exact srcTenthMat_act_entryZc wGoctadE33T32pG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE33T32p_hm : triMatF true wGoctadE33T32pL wGoctadE33T32pW = selfMatQ
    wGoctadE33T32pW := by
  rw [triMatF_eq_ZI true wGoctadE33T32pL wGoctadE33T32pW (eighthSrcMatZ.actT wGoctadE33T32pHPlan)
      (srcTenthMatZc.actT wGoctadE33T32pGPlan)
    wGoctadE33T32p_LME wGoctadE33T32p_WME,
    selfMatQ_eq_ZI wGoctadE33T32pW (srcTenthMatZc.actT wGoctadE33T32pGPlan) wGoctadE33T32p_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGoctadE33T32p_pd : labDistinct wGoctadE33T32pW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGoctadE33T32p_hpc : pairChk true (eighthSrcMatZ.actT wGoctadE33T32pHPlan) wGoctadE33T32pL
    wGoctadE33T32pW (wGoctadE33T32pW.sden * (sqSumZ wGoctadE33T32pW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE33T32p_hp : pairSumQ true wGoctadE33T32pL wGoctadE33T32pW = wGoctadE33T32pW.sden *
    (selfPairsZ wGoctadE33T32pW : ℚ) := by
  rw [selfPairsZ_of_distinct wGoctadE33T32pW wGoctadE33T32p_pd]
  exact pairSumQ_of_chk true wGoctadE33T32pL wGoctadE33T32pW (eighthSrcMatZ.actT
      wGoctadE33T32pHPlan) wGoctadE33T32p_LME wGoctadE33T32p_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
