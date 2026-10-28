/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGoctadE4T26nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamTenthM

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[8]- <-> Tenth[40]+
(record goctad:E4@T26-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGoctadE4T26n_LME : ∀ i j, wGoctadE4T26nL.mat.entry i j = (eighthSrcMatZ.actT
    wGoctadE4T26nHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE4T26nHPlan_word]
  exact eighthSrcMat_act_entryZ wGoctadE4T26nH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGoctadE4T26n_WME : ∀ i j, wGoctadE4T26nW.mat.entry i j = (srcTenthMatZc.actT
    wGoctadE4T26nGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGoctadE4T26nGPlan_word]
  exact srcTenthMat_act_entryZc wGoctadE4T26nG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGoctadE4T26n_hm : triMatF false wGoctadE4T26nL wGoctadE4T26nW = selfMatQ wGoctadE4T26nW
    := by
  rw [triMatF_eq_ZI false wGoctadE4T26nL wGoctadE4T26nW (eighthSrcMatZ.actT wGoctadE4T26nHPlan)
      (srcTenthMatZc.actT wGoctadE4T26nGPlan)
    wGoctadE4T26n_LME wGoctadE4T26n_WME,
    selfMatQ_eq_ZI wGoctadE4T26nW (srcTenthMatZc.actT wGoctadE4T26nGPlan) wGoctadE4T26n_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGoctadE4T26n_pd : labDistinct wGoctadE4T26nW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGoctadE4T26n_hpc : pairChk false (eighthSrcMatZ.actT wGoctadE4T26nHPlan) wGoctadE4T26nL
    wGoctadE4T26nW (wGoctadE4T26nW.sden * (sqSumZ wGoctadE4T26nW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGoctadE4T26n_hp : pairSumQ false wGoctadE4T26nL wGoctadE4T26nW = wGoctadE4T26nW.sden *
    (selfPairsZ wGoctadE4T26nW : ℚ) := by
  rw [selfPairsZ_of_distinct wGoctadE4T26nW wGoctadE4T26n_pd]
  exact pairSumQ_of_chk false wGoctadE4T26nL wGoctadE4T26nW (eighthSrcMatZ.actT
      wGoctadE4T26nHPlan) wGoctadE4T26n_LME wGoctadE4T26n_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
