/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE19T33pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[24]+ <-> Tenth[61]+
(record goctad:E19@T33+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGoctadE19T33p_LME : ∀ i j, wGoctadE19T33pL.mat.entry i j = (eighthSrcMatZ.actT
    wGoctadE19T33pHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE19T33pHPlan_word]
  exact eighthSrcMat_act_entryZ wGoctadE19T33pH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGoctadE19T33p_WME : ∀ i j, wGoctadE19T33pW.mat.entry i j = (srcTenthMatZc.actT
    wGoctadE19T33pGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE19T33pGPlan_word]
  exact srcTenthMat_act_entryZc wGoctadE19T33pG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE19T33p_hm : triMatF true wGoctadE19T33pL wGoctadE19T33pW = selfMatQ
    wGoctadE19T33pW := by
  rw [triMatF_eq_ZI true wGoctadE19T33pL wGoctadE19T33pW (eighthSrcMatZ.actT wGoctadE19T33pHPlan)
      (srcTenthMatZc.actT wGoctadE19T33pGPlan)
    wGoctadE19T33p_LME wGoctadE19T33p_WME,
    selfMatQ_eq_ZI wGoctadE19T33pW (srcTenthMatZc.actT wGoctadE19T33pGPlan) wGoctadE19T33p_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGoctadE19T33p_pd : labDistinct wGoctadE19T33pW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGoctadE19T33p_hpc : pairChk true (eighthSrcMatZ.actT wGoctadE19T33pHPlan) wGoctadE19T33pL
    wGoctadE19T33pW (wGoctadE19T33pW.sden * (sqSumZ wGoctadE19T33pW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE19T33p_hp : pairSumQ true wGoctadE19T33pL wGoctadE19T33pW = wGoctadE19T33pW.sden *
    (selfPairsZ wGoctadE19T33pW : ℚ) := by
  rw [selfPairsZ_of_distinct wGoctadE19T33pW wGoctadE19T33p_pd]
  exact pairSumQ_of_chk true wGoctadE19T33pL wGoctadE19T33pW (eighthSrcMatZ.actT
      wGoctadE19T33pHPlan) wGoctadE19T33p_LME wGoctadE19T33p_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
