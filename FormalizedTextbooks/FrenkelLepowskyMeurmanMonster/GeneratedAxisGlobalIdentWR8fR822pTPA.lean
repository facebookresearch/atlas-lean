/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822pTChecks
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWBase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWSelfOct
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentMatPairFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWPairD
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamRootEightM
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWFamSixthF

/-! # Factory parts (octad check, matrix, pairs) of the identification Root8[4]+ <-> Sixth[14]+
(record r8f:R822+, e = 1)

Each part of the pairing is compared in the kernel with the matching self part of the target. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveFourthIdent
set_option autoImplicit false
set_option Elab.async false

/-- Entries of the source matrix block from the plan-transported integer block. -/
theorem wR8fR822pT_LME : ∀ i j, wR8fR822pTL.mat.entry i j = (srcRootEightMatZc.actT
    wR8fR822pTHPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR822pTHPlan_word]
  exact srcRootEightMat_act_entryZc wR8fR822pTH i j

/-- Entries of the target matrix block from the plan-transported integer block. -/
theorem wR8fR822pT_WME : ∀ i j, wR8fR822pTW.mat.entry i j = (sixthSrcMatZ.actT
    wR8fR822pTGPlan).entry i j := by
  intro i j
  rw [MatZ.actT_eq, wR8fR822pTGPlan_word]
  exact sixthSrcMat_act_entryZ wR8fR822pTG i j

set_option maxRecDepth 100000 in
/-- The matrix part equals the matrix self part of the target. -/
theorem wR8fR822pT_hm : triMatF true wR8fR822pTL wR8fR822pTW = selfMatQ wR8fR822pTW := by
  rw [triMatF_eq_ZI true wR8fR822pTL wR8fR822pTW (srcRootEightMatZc.actT wR8fR822pTHPlan)
      (sixthSrcMatZ.actT wR8fR822pTGPlan)
    wR8fR822pT_LME wR8fR822pT_WME,
    selfMatQ_eq_ZI wR8fR822pTW (sixthSrcMatZ.actT wR8fR822pTGPlan) wR8fR822pT_WME]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The checked pair part (gident's packed pair lookups `pairSumZF`) against the pair self part. -/
theorem wR8fR822pT_hpc : pairChk true (srcRootEightMatZc.actT wR8fR822pTHPlan) wR8fR822pTL
    wR8fR822pTW (wR8fR822pTW.sden * (selfPairsZ wR8fR822pTW : ℚ)) = true := by
  decide +kernel

/-- The pair part equals the pair self part of the target. -/
theorem wR8fR822pT_hp : pairSumQ true wR8fR822pTL wR8fR822pTW = wR8fR822pTW.sden * (selfPairsZ
    wR8fR822pTW : ℚ) :=
  pairSumQ_of_chk true wR8fR822pTL wR8fR822pTW (srcRootEightMatZc.actT wR8fR822pTHPlan)
      wR8fR822pT_LME wR8fR822pT_hpc

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
