/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS6c4nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Sixth[8]- <-> Tenth[73]+
(record gforest:S6c4-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGoctadXGforestS6c4n_LME : ∀ i j, wGoctadXGforestS6c4nL.mat.entry i j = (sixthSrcMatZ.actT
    wGoctadXGforestS6c4nHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadXGforestS6c4nHPlan_word]
  exact sixthSrcMat_act_entryZ wGoctadXGforestS6c4nH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGoctadXGforestS6c4n_WME : ∀ i j, wGoctadXGforestS6c4nW.mat.entry i j =
    (srcTenthMatZc.actT wGoctadXGforestS6c4nGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadXGforestS6c4nGPlan_word]
  exact srcTenthMat_act_entryZc wGoctadXGforestS6c4nG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadXGforestS6c4n_hm : triMatF false wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW =
    selfMatQ wGoctadXGforestS6c4nW := by
  rw [triMatF_eq_ZI false wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW (sixthSrcMatZ.actT
      wGoctadXGforestS6c4nHPlan) (srcTenthMatZc.actT wGoctadXGforestS6c4nGPlan)
    wGoctadXGforestS6c4n_LME wGoctadXGforestS6c4n_WME,
    selfMatQ_eq_ZI wGoctadXGforestS6c4nW (srcTenthMatZc.actT wGoctadXGforestS6c4nGPlan)
        wGoctadXGforestS6c4n_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGoctadXGforestS6c4n_pd : labDistinct wGoctadXGforestS6c4nW.sh.pairs 0 = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGoctadXGforestS6c4n_hpc : pairChk false (sixthSrcMatZ.actT wGoctadXGforestS6c4nHPlan)
    wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW (wGoctadXGforestS6c4nW.sden * (sqSumZ
    wGoctadXGforestS6c4nW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGoctadXGforestS6c4n_hp : pairSumQ false wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW =
    wGoctadXGforestS6c4nW.sden * (selfPairsZ wGoctadXGforestS6c4nW : ℚ) := by
  rw [selfPairsZ_of_distinct wGoctadXGforestS6c4nW wGoctadXGforestS6c4n_pd]
  exact pairSumQ_of_chk false wGoctadXGforestS6c4nL wGoctadXGforestS6c4nW (sixthSrcMatZ.actT
      wGoctadXGforestS6c4nHPlan) wGoctadXGforestS6c4n_LME wGoctadXGforestS6c4n_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
