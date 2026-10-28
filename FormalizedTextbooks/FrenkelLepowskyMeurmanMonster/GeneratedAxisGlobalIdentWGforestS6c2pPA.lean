/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWGforestS6c2pChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamFourth

/-! # Factory parts (octad check, matrix, pairs) of the identification Fourth[18]- <-> Sixth[3]+
(record gforest:S6c2+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wGforestS6c2p_LME : ∀ i j, wGforestS6c2pL.mat.entry i j = (sixthSrcMatZ.actT
    wGforestS6c2pHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGforestS6c2pHPlan_word]
  exact sixthSrcMat_act_entryZ wGforestS6c2pH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wGforestS6c2p_WME : ∀ i j, wGforestS6c2pW.mat.entry i j = (fourthSrcMatZ.actT
    wGforestS6c2pGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wGforestS6c2pGPlan_word]
  exact fourthSrcMat_act_entryZ wGforestS6c2pG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wGforestS6c2p_hm : triMatF true wGforestS6c2pL wGforestS6c2pW = selfMatQ wGforestS6c2pW :=
    by
  rw [triMatF_eq_ZI true wGforestS6c2pL wGforestS6c2pW (sixthSrcMatZ.actT wGforestS6c2pHPlan)
      (fourthSrcMatZ.actT wGforestS6c2pGPlan)
    wGforestS6c2p_LME wGforestS6c2p_WME,
    selfMatQ_eq_ZI wGforestS6c2pW (fourthSrcMatZ.actT wGforestS6c2pGPlan) wGforestS6c2p_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wGforestS6c2p_hpc : pairChk true (sixthSrcMatZ.actT wGforestS6c2pHPlan) wGforestS6c2pL
    wGforestS6c2pW (wGforestS6c2pW.sden * (selfPairsZ wGforestS6c2pW : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wGforestS6c2p_hp : pairSumQ true wGforestS6c2pL wGforestS6c2pW = wGforestS6c2pW.sden *
    (selfPairsZ wGforestS6c2pW : ℚ) :=
  pairSumQ_of_chk true wGforestS6c2pL wGforestS6c2pW (sixthSrcMatZ.actT wGforestS6c2pHPlan)
      wGforestS6c2p_LME wGforestS6c2p_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
