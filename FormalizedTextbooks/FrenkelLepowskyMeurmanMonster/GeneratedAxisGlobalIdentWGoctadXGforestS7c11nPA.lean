/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadXGforestS7c11nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Seventh[18]- <-> Tenth[68]-
(record gforest:S7c11-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGoctadXGforestS7c11n_LME : ∀ i j, wGoctadXGforestS7c11nL.mat.entry i j =
    (srcSeventhMatZ.actT wGoctadXGforestS7c11nHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadXGforestS7c11nHPlan_word]
  exact srcSeventhMat_act_entryZ wGoctadXGforestS7c11nH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGoctadXGforestS7c11n_WME : ∀ i j, wGoctadXGforestS7c11nW.mat.entry i j =
    (srcTenthMatZc.actT wGoctadXGforestS7c11nGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadXGforestS7c11nGPlan_word]
  exact srcTenthMat_act_entryZc wGoctadXGforestS7c11nG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadXGforestS7c11n_hm : triMatF false wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW =
    selfMatQ wGoctadXGforestS7c11nW := by
  rw [triMatF_eq_ZI false wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW (srcSeventhMatZ.actT
      wGoctadXGforestS7c11nHPlan) (srcTenthMatZc.actT wGoctadXGforestS7c11nGPlan)
    wGoctadXGforestS7c11n_LME wGoctadXGforestS7c11n_WME,
    selfMatQ_eq_ZI wGoctadXGforestS7c11nW (srcTenthMatZc.actT wGoctadXGforestS7c11nGPlan)
        wGoctadXGforestS7c11n_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGoctadXGforestS7c11n_pd : labDistinct wGoctadXGforestS7c11nW.sh.pairs 0 = true := by
    decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGoctadXGforestS7c11n_hpc : pairChk false (srcSeventhMatZ.actT wGoctadXGforestS7c11nHPlan)
    wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW (wGoctadXGforestS7c11nW.sden * (sqSumZ
    wGoctadXGforestS7c11nW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGoctadXGforestS7c11n_hp : pairSumQ false wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW =
    wGoctadXGforestS7c11nW.sden * (selfPairsZ wGoctadXGforestS7c11nW : ℚ) := by
  rw [selfPairsZ_of_distinct wGoctadXGforestS7c11nW wGoctadXGforestS7c11n_pd]
  exact pairSumQ_of_chk false wGoctadXGforestS7c11nL wGoctadXGforestS7c11nW (srcSeventhMatZ.actT
      wGoctadXGforestS7c11nHPlan) wGoctadXGforestS7c11n_LME wGoctadXGforestS7c11n_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
