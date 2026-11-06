/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS7c8nChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSeventh
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamEighthT

/-! # Factory parts (octad check, matrix, pairs) of the identification Eighth[13]+ <->
Seventh[14]- (record gforest:S7c8-, e = -1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGforestS7c8n_LME : ∀ i j, wGforestS7c8nL.mat.entry i j = (srcSeventhMatZ.actT
    wGforestS7c8nHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGforestS7c8nHPlan_word]
  exact srcSeventhMat_act_entryZ wGforestS7c8nH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGforestS7c8n_WME : ∀ i j, wGforestS7c8nW.mat.entry i j = (eighthSrcMatZ.actT
    wGforestS7c8nGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGforestS7c8nGPlan_word]
  exact eighthSrcMat_act_entryZ wGforestS7c8nG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGforestS7c8n_hm : triMatF false wGforestS7c8nL wGforestS7c8nW = selfMatQ wGforestS7c8nW
    := by
  rw [triMatF_eq_ZI false wGforestS7c8nL wGforestS7c8nW (srcSeventhMatZ.actT wGforestS7c8nHPlan)
      (eighthSrcMatZ.actT wGforestS7c8nGPlan)
    wGforestS7c8n_LME wGforestS7c8n_WME,
    selfMatQ_eq_ZI wGforestS7c8nW (eighthSrcMatZ.actT wGforestS7c8nGPlan) wGforestS7c8n_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The pair labels of the target are distinct. -/
theorem wGforestS7c8n_pd : labDistinct wGforestS7c8nW.sh.pairs 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGforestS7c8n_hpc : pairChk false (srcSeventhMatZ.actT wGforestS7c8nHPlan) wGforestS7c8nL
    wGforestS7c8nW (wGforestS7c8nW.sden * (sqSumZ wGforestS7c8nW.sh.pairs : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGforestS7c8n_hp : pairSumQ false wGforestS7c8nL wGforestS7c8nW = wGforestS7c8nW.sden *
    (selfPairsZ wGforestS7c8nW : ℚ) := by
  rw [selfPairsZ_of_distinct wGforestS7c8nW wGforestS7c8n_pd]
  exact pairSumQ_of_chk false wGforestS7c8nL wGforestS7c8nW (srcSeventhMatZ.actT
      wGforestS7c8nHPlan) wGforestS7c8n_LME wGforestS7c8n_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
