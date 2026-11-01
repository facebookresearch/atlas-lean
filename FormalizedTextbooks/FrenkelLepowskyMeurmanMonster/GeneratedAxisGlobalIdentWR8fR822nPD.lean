/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPD1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPDg0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPDg1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWR8fR822nPDg2

/-! # Factory parts (odd short terms) of the identification Root8[4]- <-> Root8[4]- (record
r8f:R822-, e = -1)

The odd part of the pairing from its groups and the odd self part of the dense target as a sum
of squares (pairwise distinct odd labels). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false
set_option Elab.async false

/-- The target list in groups. -/
theorem wR8fR822nGT_groups : wR8fR822nGT = wR8fR822nGTg0 ++ (wR8fR822nGTg1 ++ (wR8fR822nGTg2)) := by
  simp only [wR8fR822nGT, wR8fR822nGTg0, wR8fR822nGTg1, wR8fR822nGTg2, List.append_assoc]

/-- The odd short part equals the odd self part of the target. -/
theorem wR8fR822n_ha : (oddWZ 64 false wR8fR822nHX wR8fR822nW : ℚ) / (2 * ((tensorWordDenAll
    wR8fR822nH : ℚ) * 32)) =
    wR8fR822nW.sden * (selfOddP wR8fR822nW : ℚ) := by
  have hz : oddWZ 64 false wR8fR822nHX wR8fR822nW = 28868608 + (33275904 + (1556480)) := by
    unfold wR8fR822nW
    rw [oddWZ_ofList, wR8fR822nGT_groups, oddSumF_append, oddSumF_append, wR8fR822n_og0,
        wR8fR822n_og1, wR8fR822n_og2]
  have hd : tensorWordDenAll wR8fR822nH = 256 := by decide +kernel
  rw [selfOddP_eq, selfOddZ_of_distinct _ wR8fR822n_odist, wR8fR822n_osq, hz, hd]
  norm_num [wR8fR822nW]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
