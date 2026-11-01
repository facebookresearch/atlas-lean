/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR81pPDg2

/-! # Factory parts (odd short terms) of the identification Root8[16]+ <-> Twelfth[24]+ (record
r8f:R81+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR81pGT_groups : wR8fR81pGT = wR8fR81pGTg0 ++ (wR8fR81pGTg1 ++ (wR8fR81pGTg2)) := by
  simp only [wR8fR81pGT, wR8fR81pGTg0, wR8fR81pGTg1, wR8fR81pGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR81p_ha : (oddWZ 112 true wR8fR81pHX wR8fR81pW : ℚ) / (2 * ((tensorWordDenAll
    wR8fR81pH : ℚ) * 32)) =
    wR8fR81pW.sden * (selfOddP wR8fR81pW : ℚ) := by
  have hz : oddWZ 112 true wR8fR81pHX wR8fR81pW = 374341632 + (377880576 + (296353792)) := by
    unfold wR8fR81pW
    rw [oddWZ_ofList, wR8fR81pGT_groups, oddSumF_append, oddSumF_append, wR8fR81p_og0,
        wR8fR81p_og1, wR8fR81p_og2]
  have hd : tensorWordDenAll wR8fR81pH = 4096 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR81p_odist, wR8fR81p_osq, hz, hd]
  norm_num [wR8fR81pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
