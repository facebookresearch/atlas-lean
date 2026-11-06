/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR86nPDg2

/-! # Factory parts (odd short terms) of the identification Root8[12]- <-> Twelfth[34]- (record
r8f:R86-, e = -1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR86nGT_groups : wR8fR86nGT = wR8fR86nGTg0 ++ (wR8fR86nGTg1 ++ (wR8fR86nGTg2)) := by
  simp only [wR8fR86nGT, wR8fR86nGTg0, wR8fR86nGTg1, wR8fR86nGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR86n_ha : (oddWZ 96 false wR8fR86nHX wR8fR86nW : ℚ) / (2 * ((tensorWordDenAll
    wR8fR86nH : ℚ) * 32)) =
    wR8fR86nW.sden * (selfOddP wR8fR86nW : ℚ) := by
  have hz : oddWZ 96 false wR8fR86nHX wR8fR86nW = 5905580032 + (6129975296 + (4741660672)) := by
    unfold wR8fR86nW
    rw [oddWZ_ofList, wR8fR86nGT_groups, oddSumF_append, oddSumF_append, wR8fR86n_og0,
        wR8fR86n_og1, wR8fR86n_og2]
  have hd : tensorWordDenAll wR8fR86nH = 65536 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR86n_odist, wR8fR86n_osq, hz, hd]
  norm_num [wR8fR86nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
