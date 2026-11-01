/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86pPDg2

/-! # Factory parts (odd short terms) of the identification Root8[12]+ <-> Twelfth[34]- (record
r8f:R86+, e = 1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR86pGT_groups : wR8fR86pGT = wR8fR86pGTg0 ++ (wR8fR86pGTg1 ++ (wR8fR86pGTg2)) := by
  simp only [wR8fR86pGT, wR8fR86pGTg0, wR8fR86pGTg1, wR8fR86pGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR86p_ha : (oddWZ 96 true wR8fR86pHX wR8fR86pW : ℚ) / (2 * ((tensorWordDenAll wR8fR86pH
    : ℚ) * 32)) =
    wR8fR86pW.sden * (selfOddP wR8fR86pW : ℚ) := by
  have hz : oddWZ 96 true wR8fR86pHX wR8fR86pW = 5905580032 + (6129975296 + (4741660672)) := by
    unfold wR8fR86pW
    rw [oddWZ_ofList, wR8fR86pGT_groups, oddSumF_append, oddSumF_append, wR8fR86p_og0,
        wR8fR86p_og1, wR8fR86p_og2]
  have hd : tensorWordDenAll wR8fR86pH = 65536 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR86p_odist, wR8fR86p_osq, hz, hd]
  norm_num [wR8fR86pW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
