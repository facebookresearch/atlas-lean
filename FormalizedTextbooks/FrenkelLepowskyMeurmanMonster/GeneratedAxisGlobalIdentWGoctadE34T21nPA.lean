/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE34T21nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[47]- <-> Tenth[26]+
(record goctad:E34@T21-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGoctadE34T21n_LME : ∀ i j, wGoctadE34T21nL.mat.entry i j = (eighthSrcMatZ.actT
    wGoctadE34T21nHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE34T21nHPlan_word]
  exact eighthSrcMat_act_entryZ wGoctadE34T21nH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGoctadE34T21n_WME : ∀ i j, wGoctadE34T21nW.mat.entry i j = (srcTenthMatZc.actT
    wGoctadE34T21nGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE34T21nGPlan_word]
  exact srcTenthMat_act_entryZc wGoctadE34T21nG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE34T21n_hm : triMatF false wGoctadE34T21nL wGoctadE34T21nW = selfMatQ
    wGoctadE34T21nW := by
  rw [triMatF_eq_ZI false wGoctadE34T21nL wGoctadE34T21nW (eighthSrcMatZ.actT wGoctadE34T21nHPlan)
      (srcTenthMatZc.actT wGoctadE34T21nGPlan)
    wGoctadE34T21n_LME wGoctadE34T21n_WME,
    selfMatQ_eq_ZI wGoctadE34T21nW (srcTenthMatZc.actT wGoctadE34T21nGPlan) wGoctadE34T21n_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGoctadE34T21n_pd : labDistinct wGoctadE34T21nW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGoctadE34T21n_hpc : pairChk false (eighthSrcMatZ.actT wGoctadE34T21nHPlan)
    wGoctadE34T21nL wGoctadE34T21nW (wGoctadE34T21nW.sden * (sqSumZ wGoctadE34T21nW.sh.pairs : ℚ))
    = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE34T21n_hp : pairSumQ false wGoctadE34T21nL wGoctadE34T21nW = wGoctadE34T21nW.sden
    * (selfPairsZ wGoctadE34T21nW : ℚ) := by
  rw [selfPairsZ_of_distinct wGoctadE34T21nW wGoctadE34T21n_pd]
  exact pairSumQ_of_chk false wGoctadE34T21nL wGoctadE34T21nW (eighthSrcMatZ.actT
      wGoctadE34T21nHPlan) wGoctadE34T21n_LME wGoctadE34T21n_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
