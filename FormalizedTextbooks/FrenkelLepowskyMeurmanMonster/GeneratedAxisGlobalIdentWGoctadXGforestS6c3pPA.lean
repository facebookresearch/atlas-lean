/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c3pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Sixth[6]+ <-> Tenth[81]-
(record gforest:S6c3+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGoctadXGforestS6c3p_LME : ∀ i j, wGoctadXGforestS6c3pL.mat.entry i j = (sixthSrcMatZ.actT
    wGoctadXGforestS6c3pHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadXGforestS6c3pHPlan_word]
  exact sixthSrcMat_act_entryZ wGoctadXGforestS6c3pH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGoctadXGforestS6c3p_WME : ∀ i j, wGoctadXGforestS6c3pW.mat.entry i j =
    (srcTenthMatZc.actT wGoctadXGforestS6c3pGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadXGforestS6c3pGPlan_word]
  exact srcTenthMat_act_entryZc wGoctadXGforestS6c3pG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadXGforestS6c3p_hm : triMatF true wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW =
    selfMatQ wGoctadXGforestS6c3pW := by
  rw [triMatF_eq_ZI true wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW (sixthSrcMatZ.actT
      wGoctadXGforestS6c3pHPlan) (srcTenthMatZc.actT wGoctadXGforestS6c3pGPlan)
    wGoctadXGforestS6c3p_LME wGoctadXGforestS6c3p_WME,
    selfMatQ_eq_ZI wGoctadXGforestS6c3pW (srcTenthMatZc.actT wGoctadXGforestS6c3pGPlan)
        wGoctadXGforestS6c3p_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGoctadXGforestS6c3p_pd : labDistinct wGoctadXGforestS6c3pW.sh.pairs 0 = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGoctadXGforestS6c3p_hpc : pairChk true (sixthSrcMatZ.actT wGoctadXGforestS6c3pHPlan)
    wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW (wGoctadXGforestS6c3pW.sden * (sqSumZ
    wGoctadXGforestS6c3pW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGoctadXGforestS6c3p_hp : pairSumQ true wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW =
    wGoctadXGforestS6c3pW.sden * (selfPairsZ wGoctadXGforestS6c3pW : ℚ) := by
  rw [selfPairsZ_of_distinct wGoctadXGforestS6c3pW wGoctadXGforestS6c3p_pd]
  exact pairSumQ_of_chk true wGoctadXGforestS6c3pL wGoctadXGforestS6c3pW (sixthSrcMatZ.actT
      wGoctadXGforestS6c3pHPlan) wGoctadXGforestS6c3p_LME wGoctadXGforestS6c3p_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
